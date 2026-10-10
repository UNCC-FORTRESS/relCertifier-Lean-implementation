/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` over the GUARDED right automaton — Theorem 3 by catch-up

`MatchMultiRatePruned.match_multi_rate_pruned` states Theorem 3 over the `⊤`-guarded two-mode
right automaton (`DRIVE`, the pruned sink `STALL`): its response runs 3/2/1/1 coupled `DRIVE`
pieces with a self-loop between pieces, and a stay `DRIVE → DRIVE` needs `0.2 ≤ v_R ≤ 1`,
which the region bookkeeping (`⊤` at `DRIVE`) does not provide.

This file states the same theorem (the declared invariant `v_L ≤ v_R`, both envelopes, the
right never in `STALL`) over the GUARDED automaton `GrPG` (every edge tests the lowered guard of
the mode it enters, `GrPG_guards`) and builds the response from the model. The right `DRIVE`
flow `v' = 1 − v`, `s' = v` moves `v_R` monotonically toward 1; the left windows (any of the
four modes, unguarded) move `v_L` toward 1 or 0.1, so `v_L` ends at most at `max(v_L, 1)` and
strictly below 1 when it started below 1 (`ode_linear_coord`: the coordinate is
`c + (v₀ − c) e^{−k r}`). After the left window the right
* makes no step when `v_R > 1` (the row holds: `v_L ≤ max(v_L, 1) ≤ v_R`);
* otherwise flows in `DRIVE` up to `b = max(v_R, 0.2, v_L)` (`< 1` unless `b = v_R`), and takes
  the stay `DRIVE → DRIVE`, legal since `b ∈ [0.2, 1]`.
No verdict pack is needed (Z3-free).
-/
import RelCertifier.Instances.MatchMultiRatePruned
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.WindowGrowth

namespace RelCertifier
namespace MatchMultiRateGuarded

open DL DLCalTiming DLRel Parse Set MatchMultiRateModal MatchMultiRatePruned

set_option linter.unusedSimpArgs false

/-! ## The guarded right automaton -/

/-- The declared edge `st → tgt` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := hostGuard vsM 2 Side.R (mRM tgt), pruned := false }

noncomputable def GrPG : SearchGraph (Var 2) :=
  { modes := [modeM 0, modeM 1], edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1] }

/-- **Faithfulness of the graph**: the same modes and edges as `GrP` (the file's `next` lists:
`DRIVE → [DRIVE, STALL]`, `STALL → [STALL]`). -/
theorem GrPG_edges : GrPG.edges.map (fun e => (e.src, e.tgt)) =
    GrP.edges.map (fun e => (e.src, e.tgt)) := rfl
theorem GrPG_modes : GrPG.modes = GrP.modes := rfl

theorem GrPG_guards : ∀ q, ∀ e ∈ GrPG.edgesFrom q,
    e.guard = hostGuard vsM 2 Side.R (mRM e.tgt) := by
  intro q e he
  have hmem : e ∈ GrPG.edges := List.mem_of_mem_filter he
  simp only [GrPG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

theorem GrPG_modeAt (q : ℕ) (hq : q < 2) : GrPG.modeAt q = some (modeM q) := by
  interval_cases q <;> rfl

theorem hltG : ∀ q, ∀ e ∈ GrPG.edgesFrom q, e.tgt < GrPG.modes.length := by
  intro q e he
  have hmem : e ∈ GrPG.edges := List.mem_of_mem_filter he
  simp only [GrPG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> norm_num [GrPG, edgeG]

theorem hRvG : ∀ q m, GrPG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  rw [show GrPG = { GrP with edges := GrPG.edges } from rfl] at hm
  exact hRvP q m (by simpa [SearchGraph.modeAt] using hm)

theorem hfreshG : ∀ q m, GrPG.modeAt q = some m → mvM ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardRM (q : ℕ) (hq : q < 2) : (hostGuard vsM 2 Side.R (mRM q)).fv ⊆ range Rv :=
  hostGuard_fv_R vsM (mRM q) (by
    interval_cases q <;>
      simp [mRM, match_multi_rate_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem hgRG : GuardsRight GrPG := by
  intro q e he
  have hmem : e ∈ GrPG.edges := List.mem_of_mem_filter he
  simp only [GrPG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hguardRM 0 (by norm_num)
  · exact hguardRM 1 (by norm_num)
  · exact hguardRM 1 (by norm_num)

theorem hm02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- `DRIVE`'s guard, evaluated (`0.2 ≤ v ≤ 1`). -/
theorem sat_guardDRIVE (x : State (Var 2)) :
    Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) x ↔ 1/5 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 := by
  simp [hostGuard, mRM, match_multi_rate_IR, Run.lowerF, Run.lowerE, hm02, hm10, vsM,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-! ## Evaluations -/

noncomputable def kL (l : ℕ) : ℝ := if l = 0 then 3 else if l = 1 then 2 else if l = 2 then 1 else 4
noncomputable def cL (l : ℕ) : ℝ := if l = 3 then 1/10 else 1

theorem fLM0_eval (l : ℕ) (hl : l < 4) (x : State (Var 2)) :
    Term.eval (fLM l 0) x = kL l * (cL l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLM, hostDyn, mLM, match_multi_rate_IR, vsM, Run.dynOf, Run.lowerE, hm10, hm3, hm2,
      hm1, hm4, hm01, hm0, hm00, hm115, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Lv, kL, cL]

theorem eval_gM (x : State (Var 2)) : Term.eval gM x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gM, gAt, atomsOf, invMPF, match_multi_rate_IR, Run.invToG, Run.lowerE, vsM,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost, Term.eval,
    AOp.interp, Lv, Rv]

theorem sat_FM (x : State (Var 2)) : Formula.sat (FM gM gsM) x ↔ x (Lv 0) ≤ x (Rv 0) := by
  rw [sat_FM_iff]
  simp only [gsM, List.mem_cons, List.not_mem_nil, or_false, forall_eq, eval_gM]
  constructor <;> intro h <;> linarith

theorem sat_domLM (x : State (Var 2)) : Formula.sat domLM x ↔
    (0 ≤ x (Lv 1) ∧ 0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ (23:ℝ)/20) := by
  simp only [domLM, hostEvolve, mLM, match_multi_rate_IR, vsM]
  simp [Run.lowerF, Run.lowerE, hm00, hm115, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
  tauto

/-! ## The left window's end: `v_L ≤ max(v_L, 1)`, and `< 1` from below 1 -/

theorem clk_mem0 (l : ℕ) :
    (Lv 0, fLM l 0) ∈ DLCalTiming.clk tgM (leftBlock (fLM l)) :=
  List.mem_append_left _ (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)

/-- One clocked piece of window `l` moves `v_L` to `c + (v_L − c) e^{−k r}`. -/
theorem piece_v (l : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 2)}
    (h : Program.sem (clockedSeg (leftBlock (fLM l)) domLM tgM dt) σ ν) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ν (Lv 0) = cL l + (σ (Lv 0) - cL l) * e := by
  obtain ⟨σ₁, hassign, ν₀, hode, htest⟩ := h
  rw [sem_test] at htest
  obtain ⟨rfl, -⟩ := htest
  rw [sem_assign] at hassign
  have h1 : σ₁ (Lv 0) = σ (Lv 0) := hassign.2 _ (by simp [Lv, Prod.ext_iff])
  obtain ⟨r, hr, hend⟩ := ode_linear_coord hode (clk_mem0 l) (kL l) (cL l)
    (fun s _ => fLM0_eval l hl s)
  have hk : 0 ≤ kL l := by unfold kL; split_ifs <;> norm_num
  refine ⟨Real.exp (-(kL l * r)), Real.exp_pos _,
    Real.exp_le_one_iff.mpr (by nlinarith), ?_⟩
  rw [hend, h1]

theorem window_box (l k : ℕ) (hl : l < 4) (dt : ℝ) (M : ℝ) (hM : 1 ≤ M) {σ ν : State (Var 2)}
    (h0 : σ (Lv 0) ≤ M)
    (h : Program.sem (windowSeg (leftBlock (fLM l)) domLM tgM dt k) σ ν) : ν (Lv 0) ≤ M := by
  refine windowSeg_preserve _ _ _ _ (fun s => s (Lv 0) ≤ M) ?_ k σ ν h0 h
  intro a b ha hab
  obtain ⟨e, he0, he1, hb⟩ := piece_v l hl dt hab
  have hc : cL l ≤ M := by unfold cL; split_ifs <;> linarith
  rw [hb]
  nlinarith

theorem window_strict (l k : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 2)}
    (h0 : σ (Lv 0) < 1)
    (h : Program.sem (windowSeg (leftBlock (fLM l)) domLM tgM dt k) σ ν) : ν (Lv 0) < 1 := by
  refine windowSeg_preserve _ _ _ _ (fun s => s (Lv 0) < 1) ?_ k σ ν h0 h
  intro a b ha hab
  obtain ⟨e, he0, he1, hb⟩ := piece_v l hl dt hab
  have hc : cL l ≤ 1 := by unfold cL; split_ifs <;> norm_num
  rw [hb]
  nlinarith

/-! ## The right `DRIVE` run, explicitly -/

noncomputable def driveEnd (ρ : State (Var 2)) (t : ℝ) : State (Var 2) :=
  fun x => if x = Rv 0 then 1 - (1 - ρ (Rv 0)) * Real.exp (-t)
    else if x = Rv 1 then ρ (Rv 1) + t - (1 - ρ (Rv 0)) * (1 - Real.exp (-t)) else ρ x

theorem driveEnd_R0 (ρ : State (Var 2)) (t : ℝ) :
    driveEnd ρ t (Rv 0) = 1 - (1 - ρ (Rv 0)) * Real.exp (-t) := by simp [driveEnd]
theorem driveEnd_R1 (ρ : State (Var 2)) (t : ℝ) :
    driveEnd ρ t (Rv 1) = ρ (Rv 1) + t - (1 - ρ (Rv 0)) * (1 - Real.exp (-t)) := by
  simp [driveEnd, show (Rv 1 : Var 2) ≠ Rv 0 from by simp [Rv, Prod.ext_iff]]
theorem driveEnd_ne (ρ : State (Var 2)) (t : ℝ) {x : Var 2} (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) :
    driveEnd ρ t x = ρ x := by simp [driveEnd, h0, h1]

theorem drive_sem (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (hw1 : ρ (Rv 0) ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Program.sem (Program.ode (modeM 0).sys (modeM 0).dom) ρ (driveEnd ρ τ) := by
  have hD := (sat_domRM ρ).mp hdom
  refine ⟨τ, fun t => driveEnd ρ t, hτ, ?_, rfl, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [driveEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [driveEnd_R1]
      · exact driveEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeM, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * (-1))
        (Set.Icc 0 τ) t := by
      have := (hasDerivAt_id t).neg.exp
      simpa using this.hasDerivWithinAt
    fin_cases i
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 0)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM0_eval 0 (by norm_num), driveEnd_R0]
      have h := (hexp.const_mul (1 - ρ (Rv 0))).const_sub 1
      refine (h.congr (fun y _ => driveEnd_R0 ρ y) (driveEnd_R0 ρ t)).congr_deriv ?_
      simp [cstM]
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 1)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM1_eval 0 (by norm_num), driveEnd_R0]
      have hid := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
      have h := ((hid.const_add (ρ (Rv 1))).sub ((hexp.const_sub 1).const_mul (1 - ρ (Rv 0))))
      refine (h.congr (fun y _ => by rw [driveEnd_R1]; simp) (by rw [driveEnd_R1]; simp)).congr_deriv
        ?_
      simp
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    have h1 : x ≠ Rv 1 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    exact driveEnd_ne ρ t h0 h1
  · intro t ht
    have he0 := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hlin : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
    refine (sat_domRM _).mpr ⟨?_, ?_, ?_⟩
    · show 0 ≤ driveEnd ρ t (Rv 1)
      rw [driveEnd_R1]
      nlinarith [hD.1, hD.2.1]
    · show 0 ≤ driveEnd ρ t (Rv 0)
      rw [driveEnd_R0]; nlinarith [hD.2.1]
    · show driveEnd ρ t (Rv 0) ≤ 23/20
      rw [driveEnd_R0]; nlinarith [hD.2.1]

/-- `DRIVE` reaches any `b ∈ [v_R, 1)` from `v_R < 1`. -/
theorem drive_reach (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (b : ℝ)
    (hwb : ρ (Rv 0) ≤ b) (hb1 : b < 1) :
    ∃ μ, Program.sem (Program.ode (modeM 0).sys (modeM 0).dom) ρ μ ∧ μ (Rv 0) = b ∧
      (∀ i, μ (Lv i) = ρ (Lv i)) := by
  have hw1 : ρ (Rv 0) < 1 := lt_of_le_of_lt hwb hb1
  have hpos : 0 < (1 - ρ (Rv 0)) / (1 - b) := div_pos (by linarith) (by linarith)
  set τ := Real.log ((1 - ρ (Rv 0)) / (1 - b)) with hτ
  have hτ0 : 0 ≤ τ := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  refine ⟨driveEnd ρ τ, drive_sem ρ hdom hw1.le τ hτ0, ?_, fun i => ?_⟩
  · have h1 : 1 - ρ (Rv 0) ≠ 0 := by linarith
    have h2 : 1 - b ≠ 0 := by linarith
    rw [driveEnd_R0, hτ, Real.exp_neg, Real.exp_log hpos, inv_div]
    field_simp
    ring
  · exact driveEnd_ne ρ τ (by simp [Lv, Rv, Prod.ext_iff]) (by simp [Lv, Rv, Prod.ext_iff])

/-! ## The guarded response -/

theorem window_framed (l k : ℕ) (hl : l < 4) (dt : ℝ) {φ : Formula (Var 2)}
    (hφ : φ.fv ⊆ range Rv) {σ ν : State (Var 2)}
    (hrun : Program.sem (windowSeg (leftBlock (fLM l)) domLM tgM dt k) σ ν) :
    Formula.sat φ σ ↔ Formula.sat φ ν :=
  sat_framed (notMem_bv_of_vars (vars_windowSegL_sub (fLM l) domLM 1 dt k (hfLM l hl) hdomLM)
    hφ) hrun

theorem window_R0 (l k : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 2)}
    (hrun : Program.sem (windowSeg (leftBlock (fLM l)) domLM tgM dt k) σ ν) :
    ν (Rv 0) = σ (Rv 0) :=
  (Program.bound_effect _ hrun (Rv 0) (fun hb => by
    rcases vars_windowSegL_sub (fLM l) domLM 1 dt k (hfLM l hl) hdomLM (Or.inr hb) with h | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h) (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))).symm

theorem sat_regionsP0 (x : State (Var 2)) : Formula.sat (regionsP 0) x :=
  sat_sinkRegions_of_lt (by decide) x

theorem not_sat_regionsP1 (x : State (Var 2)) : ¬ Formula.sat (regionsP 1) x := by
  simp [regionsP, sinkRegions, GrM, Formula.sat]

/-- **The guarded response to window `l`** (`k` pieces), from `DRIVE`. -/
theorem respondG (l k : ℕ) (hl : l < 4) (hk : 0 < k) (dt : ℝ) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM gM gsM) envM) σ) :
    GResp GrPG 0 (windowSeg (leftBlock (fLM l)) domLM tgM dt k)
      (fun qf => Formula.and (Formula.and (FM gM gsM) envM) (regionsP qf)) σ := by
  intro ν hν
  have hdomLν : Formula.sat domLM ν :=
    windowSeg_end_domL (leftBlock (fLM l)) domLM tgM dt k hk hν
  have hdomRν : Formula.sat domRM ν := (window_framed l k hl dt hdomRM hν).mp hσ.2.2
  have hRν := window_R0 l k hl dt hν
  have hrow : σ (Lv 0) ≤ σ (Rv 0) := (sat_FM σ).mp hσ.1
  have hbox : ν (Lv 0) ≤ max (σ (Lv 0)) 1 :=
    window_box l k hl dt _ (le_max_right _ _) (le_max_left _ _) hν
  set w := ν (Rv 0) with hw
  by_cases hw1 : 1 < w
  · -- no step: the row already holds
    refine ⟨[], by simp, by simp, by simp, ν, ?_, ?_⟩
    · show Program.sem (Program.test Formula.tt) ν ν
      exact ⟨rfl, trivial⟩
    · refine ⟨⟨(sat_FM ν).mpr ?_, hdomLν, hdomRν⟩, sat_regionsP0 ν⟩
      rcases le_total (σ (Lv 0)) 1 with h | h
      · rw [max_eq_right h] at hbox; linarith
      · rw [max_eq_left h] at hbox; linarith
  replace hw1 := not_lt.mp hw1
  set b := max (max w (1/5)) (ν (Lv 0)) with hb
  have hbw : w ≤ b := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb5 : (1:ℝ)/5 ≤ b := le_trans (le_max_right _ _) (le_max_left _ _)
  have hbL : ν (Lv 0) ≤ b := le_max_right _ _
  have hD := (sat_domRM ν).mp hdomRν
  -- the end state: `v_R = b`, the left as at `ν`
  obtain ⟨μ, hrun, hμR, hμL, hμdom⟩ : ∃ μ, Program.sem (Program.ode (modeM 0).sys (modeM 0).dom)
      ν μ ∧ μ (Rv 0) = b ∧ (∀ i, μ (Lv i) = ν (Lv i)) ∧ Formula.sat domRM μ := by
    by_cases hbeq : b = w
    · exact ⟨ν, sem_ode_zero _ _ hdomRν, hbeq.symm, fun _ => rfl, hdomRν⟩
    · have hb1 : b < 1 := by
        rcases le_or_gt (ν (Lv 0)) (max w (1/5)) with h | h
        · have : b = max w (1/5) := max_eq_left h
          rcases le_or_gt (1/5 : ℝ) w with h' | h'
          · exact absurd (this.trans (max_eq_left h')) hbeq
          · rw [this, max_eq_right h'.le]; norm_num
        · have hbe : b = ν (Lv 0) := max_eq_right h.le
          have hlt : σ (Lv 0) < 1 := by
            by_contra hc
            have : σ (Lv 0) = 1 := le_antisymm (by rw [← hRν] at hrow; linarith) (not_lt.mp hc)
            rw [max_eq_left (le_of_eq this.symm)] at hbox
            have := lt_of_le_of_lt (le_max_left w (1/5)) h
            linarith
          rw [hbe]; exact window_strict l k hl dt hlt hν
      obtain ⟨μ, hr, h1, h2⟩ := drive_reach ν hdomRν b hbw hb1
      exact ⟨μ, hr, h1, h2, sem_ode_ends_in_domain hr⟩
  refine ⟨[(0, modeM 0, edgeG 0 0)], ?_, by simp, by simp, μ, ?_, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨GrPG_modeAt 0 (by norm_num),
      List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩⟩
  · refine ⟨μ, sem_gseg.mpr ⟨hrun, ?_⟩, rfl, trivial⟩
    show Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) μ
    rw [sat_guardDRIVE, hμR]
    refine ⟨hb5, ?_⟩
    rcases le_total (ν (Lv 0)) 1 with h | h
    · exact max_le (max_le hw1 (by norm_num)) h
    · -- `v_L ≤ max(v_L(σ), 1)` and `v_L(σ) ≤ v_R ≤ 1`
      have : ν (Lv 0) ≤ 1 := by
        rcases le_total (σ (Lv 0)) 1 with h' | h'
        · rw [max_eq_right h'] at hbox; exact hbox
        · rw [max_eq_left h'] at hbox; rw [← hRν] at hrow; linarith
      exact max_le (max_le hw1 (by norm_num)) this
  · refine ⟨⟨(sat_FM μ).mpr (by rw [hμL 0, hμR]; exact hbL), ?_, hμdom⟩, ?_⟩
    · rw [sat_domLM, hμL 0, hμL 1]; exact (sat_domLM ν).mp hdomLν
    · simpa [qfOf, edgeG] using sat_regionsP0 μ

theorem Hmulti (dt : ℝ) :
    ∀ P ∈ leftProgsM dt, ∀ (q : ℕ), q < GrPG.modes.length → ∀ σ, σ mvM = (q : ℝ) →
      Formula.sat (Formula.and (FM gM gsM) envM) σ → Formula.sat (regionsP q) σ →
      GResp GrPG q P (fun qf => Formula.and (Formula.and (FM gM gsM) envM) (regionsP qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  have hq2 : q < 2 := hq
  match q, hq2 with
  | 1, _ => exact absurd hreg (not_sat_regionsP1 σ)
  | 0, _ =>
    simp only [leftProgsM, leftDataM, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact respondG 0 3 (by norm_num) (by norm_num) dt hσ
    · exact respondG 1 2 (by norm_num) (by norm_num) dt hσ
    · exact respondG 2 1 (by norm_num) (by norm_num) dt hσ
    · exact respondG 3 1 (by norm_num) (by norm_num) dt hσ

/-- **`match_multi_rate`, Theorem 3 over the two-mode GUARDED right automaton**, at the
declared invariant `v_L ≤ v_R`, both envelopes, and the right never in `STALL`
(`mvRegionR` at `regionsP`: `⊤` at `DRIVE`, `⊥` at `STALL`) — the statement of
`match_multi_rate_pruned` with every edge testing the entered mode's guard (`GrPG_guards`).
Response: the explicit catch-up of `respondG`, every switch legal. Z3-free; for every window
length `dt`. -/
theorem match_multi_rate_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsM dt))
      (rightAutomatonBody GrPG mvM)
      (RFormula.and (RFormula.and (canonInvM gM gsM) (envLR domLM domRM))
        (mvRegionR mvM regionsP GrPG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrPG mvM (FM gM gsM) domLM domRM regionsP
    (leftProgsM dt) (canonInvM gM gsM) (encode_canonInvM gM gsM) ?_ ?_ ?_
  · exact hdis_multi_G GrPG 0 1 dt leftDataM (by decide) hgRG hRvG hLM
  · exact hstep_assembled_GR GrPG mvM (FM gM gsM) envM regionsP (leftProgsM dt)
      hmvFM hmvenvM (fun q => notMem_sinkRegions_fv _ q mvM) hfreshG
      (guardsFresh_of_right GrPG 0 hgRG) hltG (hframesM dt) (Hmulti dt)
  · exact hddF_multiR_plain_G GrPG 0 1 dt leftDataM regionsP (canonInvM gM gsM) domLM domRM
      (by decide) hgRG hRvG hLM (fun q _ => sinkRegions_fv_sub _ q)
      (canonInvM_varsL gM gsM (by
        intro g' hg'
        simp only [gM, gsM, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gM gsM) hdomLM hdomRM

end MatchMultiRateGuarded
end RelCertifier
