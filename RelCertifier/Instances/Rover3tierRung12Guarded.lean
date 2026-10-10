/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` over the GUARDED right automaton — Theorem 3 by catch-up

`Rover3tierRung12Handoff` states the mode-keyed Theorem 3 over the `⊤`-guarded right graph
`GrQ`: its response stays in the start mode for 7 (`ACCEL`) or 4 (`COAST`) coupled pieces with
a self-loop between pieces, and a stay `ACCEL → ACCEL` needs `0.3 ≤ v_R < 0.6`, which the
right leaves while accelerating (and the bookkeeping `mvValid` does not even place `v_R` in
`[0.3, 0.6)` at the start).

This file states the same theorem (the declared mode-keyed rows, the left automaton
`ACCEL ↔ COAST` of the file, the envelope, `mvValid`) over the GUARDED graph `GrG` — every
edge tests the lowered guard of the mode it enters (`GrG_guards`) — and builds the response
directly from the model: both right modes have `v' = a`, `s' = v`, `a' = 0` with
`a ∈ [0.5, 1]`, and both rows bound the left from above by an increasing function of `v_R`
(`v_L ≤ v_R + 0.5`, `3 v_L + a_L ≤ 3 v_R + 1.2`). After the left window the right flows in its
current mode (explicit solution) until `v_R = b`, the least value `≥ max(v_R, 0.3)` that makes
the row hold, and switches there into the mode whose guard contains `b` (`ACCEL` below `0.6`,
`COAST` from `0.6`): a legal switch by the explicit end state. No verdict pack is needed.
-/
import RelCertifier.Instances.Rover3tierRung12Handoff
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.WindowGrowth

namespace RelCertifier
namespace Rover3tierRung12Guarded

open DL DLCalTiming DLRel Parse Set Rover3tierRung12Modal Rover3tierRung12Handoff

/-! ## The guarded right graph -/

/-- The declared edge `st → tgt` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsQ 3 Side.R (mRQ tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeQ 0, modeQ 1],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 0, edgeG 1 1] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range rover3tier_rung12_IR.R.modes.length).flatMap (fun q =>
      (mRQ q).next.map (fun nm => (q, rover3tier_rung12_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range rover3tier_rung12_IR.R.modes.length).flatMap (fun q =>
      (mRQ q).next.map (fun nm => (q, rover3tier_rung12_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 0), (1, 1)] := by decide
  rw [this]; rfl

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of the
mode it enters. -/
theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsQ 3 Side.R (mRQ e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 2) : GrG.modeAt q = some (modeQ q) := by
  interval_cases q <;> rfl

theorem GrG_len : GrG.modes.length = 2 := rfl

theorem hltG : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.tgt < GrG.modes.length := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrG, edgeG]

theorem hRvG : ∀ q m, GrG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeQ q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRQ q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRQ q) (Term.const 1) (hfRQ q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRQ hy

theorem hfreshG : ∀ q m, GrG.modeAt q = some m →
    mvQ ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardRQ (q : ℕ) (hq : q < 2) : (hostGuard vsQ 3 Side.R (mRQ q)).fv ⊆ range Rv :=
  hostGuard_fv_R vsQ (mRQ q) (by
    interval_cases q <;>
      simp [mRQ, rover3tier_rung12_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem hgRG : GuardsRight GrG := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hguardRQ 1 (by norm_num)
  · exact hguardRQ 0 (by norm_num)
  · exact hguardRQ 0 (by norm_num)
  · exact hguardRQ 1 (by norm_num)

theorem edgeG_mem (st tgt : ℕ) (hst : st < 2) (htgt : tgt < 2) :
    edgeG st tgt ∈ GrG.edgesFrom st := by
  refine List.mem_filter.mpr ⟨?_, by simp [edgeG]⟩
  interval_cases st <;> interval_cases tgt <;> simp [GrG]

/-- The right guards, evaluated (`ACCEL`: `0.3 ≤ v < 0.6`; `COAST`: `v ≥ 0.6`). -/
theorem sat_guardRQ (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) x ↔
      (if q = 0 then 3/10 ≤ x (Rv 0) ∧ x (Rv 0) < 3/5 else 3/5 ≤ x (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mRQ, rover3tier_rung12_IR, Run.lowerF, Run.lowerE, hq03, hq06, vsQ,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-! ## The explicit right run: `v' = a`, `s' = v`, `a' = 0` -/

noncomputable def runEnd (ρ : State (Var 3)) (τ : ℝ) : State (Var 3) :=
  fun x => if x = Rv 0 then ρ (Rv 0) + ρ (Rv 2) * τ
    else if x = Rv 1 then ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 else ρ x

theorem runEnd_ne (ρ : State (Var 3)) (τ : ℝ) {x : Var 3} (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) :
    runEnd ρ τ x = ρ x := by simp [runEnd, h0, h1]

theorem runEnd_R0 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 0) = ρ (Rv 0) + ρ (Rv 2) * τ := by
  simp [runEnd]
theorem runEnd_R1 (ρ : State (Var 3)) (τ : ℝ) :
    runEnd ρ τ (Rv 1) = ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 := by
  simp [runEnd, show (Rv 1 : Var 3) ≠ Rv 0 from by simp [Rv, Prod.ext_iff]]
theorem runEnd_R2 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 2) = ρ (Rv 2) :=
  runEnd_ne ρ τ (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
theorem runEnd_L (ρ : State (Var 3)) (τ : ℝ) (i : Fin 3) : runEnd ρ τ (Lv i) = ρ (Lv i) :=
  runEnd_ne ρ τ (by simp [Lv, Rv, Prod.ext_iff]) (by simp [Lv, Rv, Prod.ext_iff])

/-- The explicit solution is a run of either right mode, for any duration. -/
theorem run_sem (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hdom : Formula.sat domRQ ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Program.sem (Program.ode (modeQ q).sys (modeQ q).dom) ρ (runEnd ρ τ) := by
  have hD := (sat_domRQ ρ).mp hdom
  refine ⟨τ, fun t => runEnd ρ t, hτ, ?_, rfl, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [runEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [runEnd_R1]
      · exact runEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeQ, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨0, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 2) := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨0, by norm_num⟩ = fRQ q 0 from rfl, fRQ0_eval q hq, runEnd_R2]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 0) + ρ (Rv 2) * u) (ρ (Rv 2) * 1)
          (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (ρ (Rv 2))).const_add (ρ (Rv 0))
      rw [mul_one] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R0]
      · simp [runEnd_R0]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨1, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 0) + ρ (Rv 2) * t := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨1, by norm_num⟩ = fRQ q 1 from rfl, fRQ1_eval q hq, runEnd_R0]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 1) + ρ (Rv 0) * u + ρ (Rv 2) * u ^ 2 / 2)
          (ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2) (Set.Icc 0 τ) t := by
        have hu := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
        exact ((hu.const_mul (ρ (Rv 0))).const_add (ρ (Rv 1))).add
          (((hu.pow 2).const_mul (ρ (Rv 2))).div_const 2)
      have he : ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2 = ρ (Rv 0) + ρ (Rv 2) * t := by
        ring
      rw [he] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R1]
      · simp [runEnd_R1]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨2, by norm_num⟩))
          (runEnd ρ t) = 0 := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨2, by norm_num⟩ = fRQ q 2 from rfl, fRQ2_eval q hq]
        ring
      simp only [heval]
      refine HasDerivWithinAt.congr (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (ρ (Rv 2)))
        ?_ ?_
      · intro y _; simp [runEnd_R2]
      · simp [runEnd_R2]
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 0, _), List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩,
        rfl⟩)
    have h1 : x ≠ Rv 1 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 1, _), List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩,
        rfl⟩)
    exact runEnd_ne ρ t h0 h1
  · intro t ht
    refine (sat_domRQ _).mpr ?_
    simp only [runEnd_R2, runEnd_R1, runEnd_R0]
    obtain ⟨ha1, ha2, hs, hv⟩ := hD
    have ht0 := ht.1
    refine ⟨ha1, ha2, ?_, ?_⟩
    · have : 0 ≤ ρ (Rv 0) * t := mul_nonneg hv ht0
      have : 0 ≤ ρ (Rv 2) * t ^ 2 / 2 := by positivity
      linarith
    · have : 0 ≤ ρ (Rv 2) * t := mul_nonneg (by linarith) ht0
      linarith

/-! ## The catch-up response -/

/-- The target speed: at least the current `v_R` and `0.3`, enough for both rows. -/
noncomputable def target (ν : State (Var 3)) : ℝ :=
  max (max (ν (Rv 0)) (3/10))
    (max (ν (Lv 0) - 1/2) ((3 * ν (Lv 0) + ν (Lv 2) - 6/5) / 3))

theorem window_rightR (l k : ℕ) (hl : l < 2) (dt : ℝ) {σ ν : State (Var 3)}
    (hrun : Program.sem (windowSeg (leftBlock (fLQ l)) domLQ tgQ dt k) σ ν) :
    Formula.sat domRQ σ ↔ Formula.sat domRQ ν :=
  sat_framed (notMem_bv_of_vars (vars_windowSegL_sub (fLQ l) domLQ 1 dt k (hfLQ l hl) hdomLQ)
    hdomRQ) hrun

/-- **The guarded catch-up.** From any right start, for any run of left window `t`: the
right flows in its mode to `v_R = target`, then switches into `ACCEL` (`target < 0.6`, where
`target ≥ 0.3`) or `COAST` (`target ≥ 0.6`) — legal by the end state — and the row holds. -/
theorem respondG (t : ℕ) (ht : t < 2) (k : ℕ) (hk : 0 < k) (dt : ℝ) (q : ℕ) (hq : q < 2)
    {σ : State (Var 3)} (hσ : Formula.sat (Formula.and (FRow t) envQ) σ) :
    GResp GrG q (windowSeg (leftBlock (fLQ t)) domLQ tgQ dt k)
      (fun _ => Formula.and (FRow t) envQ) σ := by
  intro ν hν
  have hdomLν : Formula.sat domLQ ν :=
    windowSeg_end_domL (leftBlock (fLQ t)) domLQ tgQ dt k hk hν
  have hdomRν : Formula.sat domRQ ν := (window_rightR t k ht dt hν).mp hσ.2.2
  have hD := (sat_domRQ ν).mp hdomRν
  set b := target ν with hb
  have hb0 : ν (Rv 0) ≤ b := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb3 : (3:ℝ)/10 ≤ b := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb1 : ν (Lv 0) - 1/2 ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb2 : (3 * ν (Lv 0) + ν (Lv 2) - 6/5) / 3 ≤ b :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have ha : 0 < ν (Rv 2) := by linarith [hD.1]
  set τ := (b - ν (Rv 0)) / ν (Rv 2) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) ha.le
  have hrun := run_sem q hq ν hdomRν τ hτ0
  have hend : runEnd ν τ (Rv 0) = b := by
    rw [runEnd_R0, hτ, mul_div_cancel₀ _ ha.ne']; ring
  set qf : ℕ := if b < 3/5 then 0 else 1 with hqf
  have hqf2 : qf < 2 := by rw [hqf]; split_ifs <;> norm_num
  have hleg : SwitchLegal (edgeG q qf) (runEnd ν τ) := by
    show Formula.sat (hostGuard vsQ 3 Side.R (mRQ qf)) (runEnd ν τ)
    rw [sat_guardRQ qf hqf2, hend, hqf]
    by_cases h6 : b < 3/5
    · rw [if_pos h6, if_pos rfl]; exact ⟨hb3, h6⟩
    · rw [if_neg h6, if_neg one_ne_zero]; exact not_lt.mp h6
  refine ⟨[(q, modeQ q, edgeG q qf)], ?_, by simp, by simp, runEnd ν τ, ?_, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨GrG_modeAt q hq, edgeG_mem q qf hq hqf2⟩
  · exact ⟨runEnd ν τ, sem_gseg.mpr ⟨hrun, hleg⟩, rfl, trivial⟩
  · refine ⟨?_, ?_, sem_ode_ends_in_domain hrun⟩
    · rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · rw [sat_FRow_zero, runEnd_L, runEnd_L, hend]
        constructor <;> linarith
      · rw [sat_FRow_one, runEnd_L, runEnd_L, hend]
        linarith
    · rw [sat_domLQ, runEnd_L, runEnd_L, runEnd_L]
      exact (sat_domLQ ν).mp hdomLν

/-! ## The composed theorem over the guarded automaton -/

theorem hulRG : ulQ ∉ (rightAutomatonBody GrG mvQ).bv :=
  notMem_bv_rightAutomatonBody_G GrG mvQ ulQ (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : ulQ ∉ (mvValid mvQ GrG.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvQ GrG.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hstepMG (dt : ℝ) :
    ∀ t < (AQ dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envQ) (mvValid mvQ GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((AQ dt).window t)
      (Program.star (rightAutomatonBody GrG mvQ))
      (Formula.and (Formula.and (FRow t) envQ) (mvValid mvQ GrG.modes.length))) σ := by
  intro t ht
  rw [AQ_numModes] at ht
  have hframe : ∀ (l k : ℕ), FramesMv (windowSeg (leftBlock (fLQ l)) domLQ tgQ dt k) mvQ := by
    intro l k
    refine framesMv_window (leftBlock (fLQ l)) domLQ tgQ dt k mvQ (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLQ l) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · rw [AQ_window_zero]
    exact hstepMode_GF GrG mvQ (FRow 0) envQ _ (aux_notin_FRow 0 0) hmvenvQ hfreshG
      (guardsFresh_of_right GrG 0 hgRG) hltG (hframe 0 7)
      (fun q hq σ _ hσ => respondG 0 (by norm_num) 7 (by norm_num) dt q hq hσ)
  · rw [AQ_window_one]
    exact hstepMode_GF GrG mvQ (FRow 1) envQ _ (aux_notin_FRow 0 1) hmvenvQ hfreshG
      (guardsFresh_of_right GrG 0 hgRG) hltG (hframe 1 4)
      (fun q hq σ _ hσ => respondG 1 (by norm_num) 4 (by norm_num) dt q hq hσ)

/-- **`rover3tier_rung12`, Theorem 3 at the DECLARED mode-dependent invariant, over the
GUARDED right automaton.** `u_L`-keyed rows (`ACCEL`: `v[l] ≤ v[r] + 0.5 ∧ 3v[l] + a[l] ≤
3v[r] + 1.2`; `COAST`: `3v[l] + a[l] ≤ 3v[r] + 1.2`) over the left automaton of the file
(`ACCEL ↔ COAST`, guard-tested, windows of 7 and 4 clocked pieces), against the file's right
automaton with every edge testing the entered mode's guard (`GrG_guards`). Loop invariant:
the rows, the envelope, `mvValid`. Response: the explicit catch-up of `respondG`, every switch
legal. Z3-free; for every window length `dt`. -/
theorem rover3tier_rung12_modeKeyed_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AQ dt) ulQ)
      (rightAutomatonBody GrG mvQ)
      (psiK ulQ ϕRow (AQ dt).numModes domLQ domRQ
        (mvValidR mvQ GrG.modes.length))) := by
  refine theorem3_modeKeyed (AQ dt) ulQ GrG mvQ FRow ϕRow domLQ domRQ
    (mvValid mvQ GrG.modes.length) (mvValidR mvQ GrG.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (AQ dt) GrG 0 1 2 (by decide) (by decide) (hwinQ dt) (hgrdQ dt)
      (hnextQ dt) hgRG hRvG
  · exact hstep_modeKeyed (AQ dt) ulQ (rightAutomatonBody GrG mvQ) FRow envQ
      (mvValid mvQ GrG.modes.length) (aux_notin_FRow 2) hulenvQ hulBkG (hulGQ dt)
      (hframesUlQ dt) hulRG (hnextQ dt) (hstepMG dt) (handoffQ dt)
  · exact hddF_modeKeyed_G (AQ dt) GrG 0 1 2 (by decide) (by decide) ϕRow domLQ domRQ
      (mvValidR mvQ GrG.modes.length) (hwinQ dt) (hgrdQ dt) (hnextQ dt) hgRG hRvG
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsL gQ gsQ (fun g' hg' => by
            simp only [gQ, gsQ, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl <;> exact hgAt _)
        | succ m => exact canonInvM_varsL gQC gsQC (fun g' hg' => by
            simp only [gQC, gsQC, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl <;> exact hgAtC _))
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsR gQ gsQ
        | succ m => exact canonInvM_varsR gQC gsQC)
      hdomLQ hdomRQ rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvQ GrG.modes.length hv))

end Rover3tierRung12Guarded
end RelCertifier
