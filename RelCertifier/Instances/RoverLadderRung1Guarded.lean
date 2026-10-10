/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3` over the GUARDED right automaton — Theorem 3 by a climb

`RoverLadderRung1Modal.rover_ladder_rung1_modal` states Theorem 3 over the `⊤`-guarded right
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. Over the guarded chain with that
cut-only invariant the statement is false (a `STEEP` right at `s_R = 5` has no step; history
in `docs/GUARDED-SWITCHING.md`). This file states Theorem 3 over the GUARDED graph `GrG` (every edge tests the lowered
guard of the mode it enters, `GrG_guards`) at the mode-consistent region: the right in the
guard of its current mode (`gregion`; no cut is kept on this benchmark).

The response is the model's own climb. Both rows bound the deployed from above by the
reference (`v_L ≤ v_R`, `s_L ≤ s_R + 0.2`), every right band's guard caps `v_R` by the band's
set point (`0.3`, `0.5`, `0.65`), so along the climb `v_R` only grows; a left window ends with
`v_L` either no higher than at its start or strictly below `0.65` (`windowSeg_coord_le_or_lt`).
After the window the right runs its band to the next band's floor and switches there (legal by
the explicit end state), then holds `FLAT` until `v_R ≥ v_L` and `s_R ≥ s_L − 0.2`, and takes
the self-loop. Every run is the explicit exponential solution (`explicit_run`). Z3-free.
-/
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadderRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung1Modal

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

/-! ## The climb -/

/-- **The `FLAT` hold**: from a `FLAT` state in its guard, run until `v_R ≥ V` (any target `V`
strictly below the set point `0.65`, or already reached) and `s_R ≥ S`, then the self-loop. -/
theorem climbFlat (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (hg : 7/5 ≤ ρ (Rv 1) ∧ ρ (Rv 0) ≤ 13/20) (V S : ℝ) (hV : V < 13/20 ∨ V ≤ ρ (Rv 0))
    {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domRE μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp GrG 2 post ρ := by
  have hD := (sat_domRE ρ).mp hdom
  have hc2 : cstE 2 = 13/20 := by norm_num [cstE]
  -- the hold's length: enough for `V` (when below the set point) and for `S`
  set δ : ℝ := if V < 13/20 then 13/20 - V else 1 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; split_ifs with h
    · linarith
    · norm_num
  set τ : ℝ := (13/20) / (3 * δ) + max 0 ((S - ρ (Rv 1) + 1) * (20/13)) with hτ
  have hτ1 : 0 ≤ (13/20) / (3 * δ) := by positivity
  have hτ2 : 0 ≤ max 0 ((S - ρ (Rv 1) + 1) * (20/13)) := le_max_left _ _
  have hτ0 : 0 ≤ τ := by linarith
  have hrun := runE_sem 2 (by norm_num) ρ hdom τ hτ0
  set μ := runE 2 ρ τ with hμ
  have hmono := runE_v_mono 2 ρ (by rw [hc2]; exact hg.2) hτ0
  rw [hc2] at hmono
  have hslow := runE_s_low 2 (by norm_num) ρ hD.2.1 hτ0
  rw [hc2] at hslow
  have hμdom : Formula.sat domRE μ := sem_ode_ends_in_domain hrun
  have hμL : ∀ i, μ (Lv i) = ρ (Lv i) := runE_L 2 ρ τ
  have hvV : V ≤ μ (Rv 0) := by
    rcases hV with hV | hV
    · have hδV : δ = 13/20 - V := by rw [hδ, if_pos hV]
      -- `e^{−3τ} · 0.65 < δ` from `e^{3τ} ≥ 1 + 3τ > 0.65/δ`
      have he := Real.add_one_le_exp (3 * τ)
      have hinv : Real.exp (-(3 * τ)) * Real.exp (3 * τ) = 1 := by
        rw [← Real.exp_add]; simp
      have h3τ : (13/20) / δ ≤ 3 * τ := by
        have : 3 * ((13/20) / (3 * δ)) = (13/20) / δ := by field_simp
        linarith
      have h1 : (13/20) < δ * Real.exp (3 * τ) := by
        have : (13/20) / δ * δ = 13/20 := by field_simp
        nlinarith
      have hle : Real.exp (-(3 * τ)) * (13/20) < δ := by
        nlinarith [Real.exp_pos (-(3 * τ))]
      have hv0 := hD.2.1
      rw [hμ, runE_v, hc2]
      nlinarith [Real.exp_pos (-(3 * τ))]
    · exact le_trans hV hmono.1
  have hsS : S ≤ μ (Rv 1) := by
    have hm : (S - ρ (Rv 1) + 1) * (20/13) ≤ max 0 ((S - ρ (Rv 1) + 1) * (20/13)) :=
      le_max_right _ _
    have : 13/20 * τ ≥ 13/20 * ((S - ρ (Rv 1) + 1) * (20/13)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    nlinarith [hslow.1]
  have hs14 : 7/5 ≤ μ (Rv 1) := le_trans hg.1 hslow.2
  refine rresp_step (GrG_modeAt 2 (by norm_num)) (edgeG_mem 2 2 (by simp [GrG])) hrun ?_
    (rresp_stop (hpost μ hμL hμdom hs14 hmono.2 hmono.1 hvV hsS))
  show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) μ
  rw [sat_guardR2]
  exact ⟨hs14, hmono.2⟩

/-- **The climb from `MODER`** (guard `0.6 ≤ s < 1.4`, `v ≤ 0.5`): run to `s = 1.4`, switch into
`FLAT` (legal), then the hold. -/
theorem climbModer (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (hg : 3/5 ≤ ρ (Rv 1) ∧ ρ (Rv 1) < 7/5 ∧ ρ (Rv 0) ≤ 1/2) (V S : ℝ)
    (hV : V < 13/20 ∨ V ≤ ρ (Rv 0)) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domRE μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp GrG 1 post ρ := by
  have hD := (sat_domRE ρ).mp hdom
  have hc1 : cstE 1 = 1/2 := by norm_num [cstE]
  obtain ⟨τ, hτ, hτs⟩ := runE_reach 1 (by norm_num) ρ hD.2.1 (7/5) (le_of_lt hg.2.1)
  have hrun := runE_sem 1 (by norm_num) ρ hdom τ hτ
  set κ := runE 1 ρ τ with hκ
  have hmono := runE_v_mono 1 ρ (by rw [hc1]; exact hg.2.2) hτ
  rw [hc1] at hmono
  have hκdom : Formula.sat domRE κ := sem_ode_ends_in_domain hrun
  refine rresp_step (GrG_modeAt 1 (by norm_num)) (edgeG_mem 1 2 (by simp [GrG])) hrun ?_ ?_
  · show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) κ
    rw [sat_guardR2]
    exact ⟨le_of_eq hτs.symm, by linarith [hmono.2]⟩
  · refine climbFlat κ hκdom ⟨le_of_eq hτs.symm, by linarith [hmono.2]⟩ V S
      (hV.imp_right (fun h => le_trans h hmono.1)) ?_
    intro μ hμL hμd h1 h2 h3 h4 h5
    exact hpost μ (fun i => (hμL i).trans (runE_L 1 ρ τ i)) hμd h1 h2 (le_trans hmono.1 h3) h4 h5

/-- **The climb from `STEEP`** (guard `s < 0.6`, `v ≤ 0.3`): run to `s = 0.6`, switch into
`MODER` (legal), then `climbModer`. -/
theorem climbSteep (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (hg : ρ (Rv 1) < 3/5 ∧ ρ (Rv 0) ≤ 3/10) (V S : ℝ)
    (hV : V < 13/20 ∨ V ≤ ρ (Rv 0)) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domRE μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp GrG 0 post ρ := by
  have hD := (sat_domRE ρ).mp hdom
  have hc0 : cstE 0 = 3/10 := by norm_num [cstE]
  obtain ⟨τ, hτ, hτs⟩ := runE_reach 0 (by norm_num) ρ hD.2.1 (3/5) (le_of_lt hg.1)
  have hrun := runE_sem 0 (by norm_num) ρ hdom τ hτ
  set κ := runE 0 ρ τ with hκ
  have hmono := runE_v_mono 0 ρ (by rw [hc0]; exact hg.2) hτ
  rw [hc0] at hmono
  have hκdom : Formula.sat domRE κ := sem_ode_ends_in_domain hrun
  refine rresp_step (GrG_modeAt 0 (by norm_num)) (edgeG_mem 0 1 (by simp [GrG])) hrun ?_ ?_
  · show Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) κ
    rw [sat_guardR1]
    exact ⟨le_of_eq hτs.symm, by rw [hτs]; norm_num, by linarith [hmono.2]⟩
  · refine climbModer κ hκdom ⟨le_of_eq hτs.symm, by rw [hτs]; norm_num, by linarith [hmono.2]⟩
      V S (hV.imp_right (fun h => le_trans h hmono.1)) ?_
    intro μ hμL hμd h1 h2 h3 h4 h5
    exact hpost μ (fun i => (hμL i).trans (runE_L 0 ρ τ i)) hμd h1 h2 (le_trans hmono.1 h3) h4 h5

/-! ## The guarded response to a left window -/

theorem he1 : Run.parseRat "1" = some 1 := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hem1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fLE0_eval (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval (fLE l 0) x = 3 * (cstE l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLE, hostDyn, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, he1, he05, hem1, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv, cstE]

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 3)}
    (h : Program.sem (windowSeg (leftBlock (fLE l)) domLE tgE dt 1) σ ν) (i : Fin 3) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLE l) domLE 1 dt 1 (hfLE l hl) hdomLE
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sat_FE (x : State (Var 3)) : Formula.sat (FM gE gsE) x ↔
    (x (Lv 0) - x (Rv 0) ≤ 0 ∧ x (Lv 1) - (x (Rv 1) + 1/5) ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt0_eval, gAt1_eval]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): climb the
chain and hold `FLAT` until both rows hold. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM gE gsE) envE) σ)
    (hguard : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) σ) :
    GResp GrG q (windowSeg (leftBlock (fLE l)) domLE tgE dt 1)
      (fun _ => Formula.and (Formula.and (FM gE gsE) envE) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLE l) domLE tgE dt 0 3 (cstE l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLE0_eval l hl s) 1 hwin
  have hrow := (sat_FE σ).mp hσ.1
  have hdomLν : Formula.sat domLE ν :=
    windowSeg_end_domL (leftBlock (fLE l)) domLE tgE dt 1 (by norm_num) hwin
  have hdomRν : Formula.sat domRE ν := by
    rw [sat_domRE, hR 0, hR 1]; exact (sat_domRE σ).mp hσ.2.2
  have hgν : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) ν :=
    frames_right (vars_windowSegL_sub (fLE l) domLE 1 dt 1 (hfLE l hl) hdomLE)
      (hguardR_all q) hwin hguard
  have hcl := cstE_bounds l hl
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; linarith [hcl.2]
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRE μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM gE gsE) envE) Formula.tt) μ := by
    intro μ hμL hμd _ _ _ hv hs
    refine ⟨⟨(sat_FE μ).mpr ⟨by rw [hμL 0]; linarith, by rw [hμL 1]; linarith⟩, ?_, hμd⟩,
      trivial⟩
    refine (Formula.coincidence domLE (fun x hx => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLE hx
    exact hμL i
  interval_cases q
  · rw [sat_guardR0] at hgν
    exact climbSteep ν hdomRν ⟨hgν.2.1, hgν.2.2⟩ _ _ hV hfin
  · rw [sat_guardR1] at hgν
    exact climbModer ν hdomRν hgν _ _ hV hfin
  · rw [sat_guardR2] at hgν
    exact climbFlat ν hdomRν hgν _ _ hV hfin

/-! ## Theorem 3 over the guarded automaton -/

/-- **`refinement_ladder_rover_rung1_2to3`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The left: the file's three windows (`bigChoice`, one clocked piece of
at most `dt` each), the right: the file's chain `STEEP → MODER → FLAT` with every edge testing
the entered band's guard (`GrG_guards`). Loop invariant: the declared rows
`v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`, both envelopes, and the right in the guard of its current band
(`mvRegionR` at `gregion`). Response: the explicit climb (`respondG`). Z3-free; for every
window length `dt`. -/
theorem rover_ladder_rung1_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsE dt))
      (rightAutomatonBody GrG mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvRegionR mvE gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvE (FM gE gsE) domLE domRE gregion
    (leftProgsE dt) (canonInvM gE gsE) (encode_canonInvM gE gsE) ?_ ?_ ?_
  · exact hdis_multi_G GrG 0 1 dt leftDataE (by decide) hgRG hRvG hLE
  · refine hstep_assembled_GR GrG mvE (FM gE gsE) envE gregion (leftProgsE dt)
      hmvFE hmvenvE hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesE dt) ?_
    refine Hmulti_regionG GrG mvE _ (fun _ => Formula.tt) GrG_guards (FM gE gsE) envE
      (leftProgsE dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsE, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_windowSegL_sub d.1 d.2.1 1 dt d.2.2 (hLE d hd).1 (hLE d hd).2)
        (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsE, leftDataE, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_plain_G GrG 0 1 dt leftDataE gregion (canonInvM gE gsE) domLE domRE
      (by decide) hgRG hRvG hLE (fun q _ => gregion_fv q)
      (canonInvM_varsL gE gsE (by
        intro g' hg'
        simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gE gsE) hdomLE hdomRE

end RoverLadderRung1Guarded
end RelCertifier
