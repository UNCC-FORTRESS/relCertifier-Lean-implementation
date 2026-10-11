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
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.match_multi_rate

namespace RelCertifier
namespace MatchMultiRateGuarded

open DL DLCalTiming DLRel Parse Set MatchMultiRateModal MatchMultiRatePruned RelCertifier.Oracle

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

/-- The instance's explicit `DRIVE` run (`drive_sem`), with its duration kept. -/
theorem drive_sol (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (hw1 : ρ (Rv 0) ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeM 0).sys (modeM 0).dom ρ τ (fun t => driveEnd ρ t) := by
  have hD := (sat_domRM ρ).mp hdom
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩
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

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

theorem hm05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hm07 : Run.parseRat "0.7" = some ((7:ℚ)/10) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hm095 : Run.parseRat "0.95" = some ((19:ℚ)/20) := by
  have h : parseQ "0.95" = some (⟨95, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

noncomputable def guardM (l : ℕ) : Formula (Var 2) := hostGuard vsM 2 Side.L (mLM l)

theorem hguardL (l : ℕ) (hl : l < 4) : (guardM l).fv ⊆ range Lv :=
  hostGuard_fv_L vsM (mLM l) (by interval_cases l <;> decide)

noncomputable def cAL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vsM 2 Side.L (cutAtomsOfX match_multi_rate_cutsV2X.L (mLM l).name)
noncomputable def cAR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vsM 2 Side.R (cutAtomsOfX match_multi_rate_cutsV2X.R (mRM q).name)

def aGe (k : String) : PForm := .cmp ">=" (.var "v") (.num k)
def aLe (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def lStr (l : ℕ) : String := if l = 0 then "0.2" else if l = 1 then "0.5" else "0.7"
noncomputable def lK (l : ℕ) : ℝ := if l = 0 then 1/5 else if l = 1 then 1/2 else 7/10

theorem gL_ge (l : ℕ) (hl : l < 3) : hostAtomG vsM 2 Side.L (aGe (lStr l)) = thrGe (Lv 0) (lK l) := by
  interval_cases l <;>
  simp [aGe, lStr, lK, hostAtomG, cutAtomG, Run.lowerE, hm02, hm05, hm07, vsM,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gL_le : hostAtomG vsM 2 Side.L (aLe "1.0") = thrLe (Lv 0) 1 := by
  simp [aLe, hostAtomG, cutAtomG, Run.lowerE, hm10, vsM,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Lv]
theorem gR_ge : hostAtomG vsM 2 Side.R (aGe "0.2") = thrGe (Rv 0) (1/5) := by
  simp [aGe, hostAtomG, cutAtomG, Run.lowerE, hm02, vsM,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gR_le : hostAtomG vsM 2 Side.R (aLe "1.0") = thrLe (Rv 0) 1 := by
  simp [aLe, hostAtomG, cutAtomG, Run.lowerE, hm10, vsM,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Rv]

theorem cAL_eq (l : ℕ) (hl : l < 3) :
    cAL l = [(hostAtomF vsM 2 Side.L (aGe (lStr l)), thrGe (Lv 0) (lK l)),
      (hostAtomF vsM 2 Side.L (aLe "1.0"), thrLe (Lv 0) 1)] := by
  rw [← gL_ge l hl, ← gL_le]; interval_cases l <;> rfl
theorem gL_ge01 : hostAtomG vsM 2 Side.L (aGe "0.1") = thrGe (Lv 0) (1/10) := by
  simp [aGe, hostAtomG, cutAtomG, Run.lowerE, hm01, vsM,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem cAL_three : cAL 3 = [(hostAtomF vsM 2 Side.L (aLe "1.0"), thrLe (Lv 0) 1),
    (hostAtomF vsM 2 Side.L (aGe "0.1"), thrGe (Lv 0) (1/10))] := by
  rw [← gL_ge01, ← gL_le]; rfl
theorem cAR_eq : cAR 0 = [(hostAtomF vsM 2 Side.R (aGe "0.2"), thrGe (Rv 0) (1/5)),
    (hostAtomF vsM 2 Side.R (aLe "1.0"), thrLe (Rv 0) 1)] := by
  rw [← gR_ge, ← gR_le]; rfl

theorem hiffL (l : ℕ) (hl : l < 4) : AtomsIff (cAL l) := by
  by_cases h3 : l = 3
  · subst h3; rw [cAL_three]
    intro a ha ν
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [← gL_le]; exact hostAtom_iff (vars := vsM) (side := Side.L) (op := "<=") (x := .var "v") (y := .num "1.0") (Or.inl rfl) ν
    · rw [← gL_ge01]; exact hostAtom_iff (vars := vsM) (side := Side.L) (op := ">=") (x := .var "v") (y := .num "0.1") (Or.inr rfl) ν
  rw [cAL_eq l (by omega)]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [← gL_ge l (by omega)]; unfold aGe; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_le]; exact hostAtom_iff (vars := vsM) (side := Side.L) (op := "<=") (x := .var "v") (y := .num "1.0") (Or.inl rfl) ν
theorem hiffR : AtomsIff (cAR 0) := by
  rw [cAR_eq]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [← gR_ge]; exact hostAtom_iff (vars := vsM) (side := Side.R) (op := ">=") (x := .var "v") (y := .num "0.2") (Or.inr rfl) ν
  · rw [← gR_le]; exact hostAtom_iff (vars := vsM) (side := Side.R) (op := "<=") (x := .var "v") (y := .num "1.0") (Or.inl rfl) ν

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 4) :
    ∀ ν, Formula.sat (hostGuard vsM 2 Side.L (mLM l)) ν → CutSat (cAL l) ν := by
  intro ν hν
  refine cutSatL_of_guard match_multi_rate_cutsV2X_wf (mLM l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, match_multi_rate_cutsV2X, mLM, match_multi_rate_IR] at hx
      try (rcases hx with rfl | rfl <;> simp)
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, match_multi_rate_cutsV2X, mLM, match_multi_rate_IR] at hx
      try (rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hm01, hm02, hm05, hm07, hm10, vsM, Run.resolveVar,
          List.findIdx?_cons])
  · interval_cases l <;>
      simp [mLM, match_multi_rate_IR, Run.lowerF, Run.lowerE, hm01, hm02, hm05, hm07, hm095, hm10, vsM,
        Run.resolveVar, List.findIdx?_cons]

theorem hO1R :
    ∀ ν, Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) ν → CutSat (cAR 0) ν := by
  intro ν hν
  refine cutSatR_of_guard match_multi_rate_cutsV2X_wf (mRM 0) rfl ?_ ?_ ?_ ν hν
  · intro x hx
    simp [cutAtomsOfX, match_multi_rate_cutsV2X, mRM, match_multi_rate_IR] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx
    simp [cutAtomsOfX, match_multi_rate_cutsV2X, mRM, match_multi_rate_IR] at hx
    rcases hx with rfl | rfl <;>
      simp [Run.lowerF, Run.lowerE, hm02, hm10, vsM, Run.resolveVar, List.findIdx?_cons]
  · simp [mRM, match_multi_rate_IR, Run.lowerF, Run.lowerE, hm02, hm10, vsM,
      Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem kL_pos (l : ℕ) : 0 < kL l := by
  unfold kL; split_ifs <;> norm_num

theorem stayL (l : ℕ) (hl : l < 4) (c : ℝ) :
    AtomsStayC (cAL l) (jointSys (fLM l) (fRM 0) (Term.const c)) (Formula.and domLM domRM) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  by_cases h3 : l = 3
  · subst h3
    rw [cAL_three] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrLe_L 0 1 _ _ _ _ (Formula.and domLM domRM) (fun x h => h)
        (fun z _ hK => by
          rw [fLM0_eval 3 (by norm_num)]; simp only [kL, cL]; norm_num; linarith) hinit
    · exact boxle_thrGe_L 0 (1/10) _ _ _ _ (Formula.and domLM domRM) (fun x h => h)
        (fun z _ hK => by
          rw [fLM0_eval 3 (by norm_num)]; simp only [kL, cL]; norm_num; linarith) hinit
  have hl3 : l < 3 := by omega
  have hc1 : cL l = 1 := by unfold cL; simp [h3]
  rw [cAL_eq l hl3] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_L 0 (lK l) _ _ _ _ (Formula.and domLM domRM) (fun x h => h)
      (fun z _ hK => by
        rw [fLM0_eval l hl, hc1]
        have : lK l ≤ 7/10 := by unfold lK; split_ifs <;> norm_num
        exact mul_nonneg (kL_pos l).le (by linarith)) hinit
  · exact boxle_thrLe_L 0 1 _ _ _ _ (Formula.and domLM domRM) (fun x h => h)
      (fun z _ hK => by
        rw [fLM0_eval l hl, hc1]
        exact mul_nonpos_of_nonneg_of_nonpos (kL_pos l).le (by linarith)) hinit

theorem stayR_gen (fL : Fin 2 → Term (Var 2)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 2)) :
    AtomsStayC (cAR 0) (jointSys fL (fRM 0) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR a ha ν).mp (hν a ha)
  rw [cAR_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 0 (1/5) _ _ c hc D D (fun x h => h)
      (fun z _ hK => by rw [fRM0_eval 0 (by norm_num)]; simp only [cstM, if_true]; linarith) hinit
  · exact boxle_thrLe_R 0 1 _ _ c hc D D (fun x h => h)
      (fun z _ hK => by rw [fRM0_eval 0 (by norm_num)]; simp only [cstM, if_true]; linarith) hinit

/-! ## The invariant's component, as the tool lowers it -/

theorem comps_eq : hostComps vsM 2
    (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2 = [gAt 0] := by
  have hrow : (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2 = invMPF := rfl
  have hlist : pAtoms invMPF = [(atomsOf invMPF).getD 0 .tt] := by decide
  rw [hrow, hostComps_atoms vsM invMPF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdL : ("L_v".drop 2).copy = "v" := by decide
    have hdR : ("R_v".drop 2).copy = "v" := by decide
    subst ha
    exact ⟨⟨_, _, _, rfl⟩, by
      simp [atomsOf, invMPF, match_multi_rate_IR, Run.invToG, Run.lowerE,
        vsM, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ gM :: gsM, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gM, gsM, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc; exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at `DRIVE`, at the cover's λ (`FAST` 3, `MEDIUM` 2, `SLOW` and
`RESET` 1), strata `[0]`. -/
def Verd : ℕ → ℕ → Prop
  | 0, q => modalVerdX match_multi_rate_IRv2 match_multi_rate_cutsV2X 2 0 [0] 3 0 q
  | 1, q => modalVerdX match_multi_rate_IRv2 match_multi_rate_cutsV2X 2 0 [0] 2 1 q
  | l, q => modalVerdX match_multi_rate_IRv2 match_multi_rate_cutsV2X 2 0 [0] 1 l q

noncomputable def lamOf : ℕ → ℝ
  | 0 => 3
  | 1 => 2
  | _ => 1

theorem lamOf_pos (l : ℕ) : 0 < lamOf l := by
  match l with
  | 0 => norm_num [lamOf]
  | 1 => norm_num [lamOf]
  | _ + 2 => show (0:ℝ) < 1; norm_num

theorem domL_univ (l : ℕ) (hl : l < 4) : hostEvolve vsM 2 Side.L (mLM l) = domLM := by
  interval_cases l <;> rfl

theorem verd_core (l : ℕ) (hl : l < 4) (h : Verd l 0) :
    VerdXCore (gM :: gsM) (fLM l) (fRM 0) (lamOf l)
      (domCutX (Formula.and domLM domRM) (cAL l) (cAR 0)) := by
  rw [← domL_univ l hl]
  have hR : hostEvolve vsM 2 Side.R (mRM 0) = domRM := rfl
  rw [← hR]
  interval_cases l
  · have h' : VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsM 2
        (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLM 0) (fRM 0) 3 (domCutX (Formula.and (hostEvolve vsM 2 Side.L (mLM 0))
          (hostEvolve vsM 2 Side.R (mRM 0))) (cAL 0) (cAR 0)) := h
    rw [comps_eq] at h'
    simpa [gM, gsM, lamOf] using h'
  · have h' : VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsM 2
        (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLM 1) (fRM 0) 2 (domCutX (Formula.and (hostEvolve vsM 2 Side.L (mLM 1))
          (hostEvolve vsM 2 Side.R (mRM 0))) (cAL 1) (cAR 0)) := h
    rw [comps_eq] at h'
    simpa [gM, gsM, lamOf] using h'
  · have h' : VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsM 2
        (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLM 2) (fRM 0) 1 (domCutX (Formula.and (hostEvolve vsM 2 Side.L (mLM 2))
          (hostEvolve vsM 2 Side.R (mRM 0))) (cAL 2) (cAR 0)) := h
    rw [comps_eq] at h'
    simpa [gM, gsM, lamOf] using h'
  · have h' : VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsM 2
        (match_multi_rate_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLM 3) (fRM 0) 1 (domCutX (Formula.and (hostEvolve vsM 2 Side.L (mLM 3))
          (hostEvolve vsM 2 Side.R (mRM 0))) (cAL 3) (cAR 0)) := h
    rw [comps_eq] at h'
    simpa [gM, gsM, lamOf] using h'

/-! ## The anchor of the cover's pair `(l, DRIVE)` -/

noncomputable def anc (l : ℕ) (_q : ℕ) : Formula (Var 2) := FM gM (gsM ++ atomTerms (cAL l) (cAR 0))

theorem cAL_fv (l : ℕ) (hl : l < 4) : ∀ a ∈ cAL l, a.2.fv ⊆ range Lv := by
  intro a ha
  by_cases h3 : l = 3
  · subst h3
    rw [cAL_three] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp
  rw [cAL_eq l (by omega)] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp

theorem cAR_fv : ∀ a ∈ cAR 0, a.2.fv ⊆ range Rv := by
  intro a ha
  rw [cAR_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp

theorem anc_fv (l q : ℕ) (hl : l < 4) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_contra hS
  refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact comps_fv _ List.mem_cons_self hxg
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact comps_fv _ (List.mem_cons_of_mem _ hg') hxg
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
  rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl (cAL_fv l hl a ha hxg)
  · exact Or.inr (cAR_fv a ha hxg)

theorem anc_box (l : ℕ) (hl : l < 4) (hv : Verd l 0) :
    ∀ σ ω, Formula.sat (anc l 0) σ →
      Program.sem (Program.ode (jointSys (fLM l) (fRM 0) (Term.const (lamOf l)))
        (Formula.and domLM domRM)) σ ω → Formula.sat (anc l 0) ω :=
  couple_box_cutX gM gsM (gM :: gsM) (cAL l) (cAR 0) (fLM l) (fRM 0) (lamOf l) domLM domRM
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) hiffR (stayL l hl _)
    (stayR_gen (fLM l) _ (lamOf_pos l).le _) (verd_core l hl hv)

theorem anc_iff (l : ℕ) (hl : l < 4) (q : ℕ) (x : State (Var 2)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gM gsM) x ∧ CutSat (cAL l) x ∧ CutSat (cAR 0) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) hiffR]

theorem FMM_fv : (FM gM gsM).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv c hc hvc)) hv

/-! ## The right's move: `DRIVE` keeps its guard (`v_R` climbs toward 1 from `[0.2, 1]`) -/

/-- A right state at `DRIVE`, in its guard and the envelope. -/
def PreM (q : ℕ) (x : State (Var 2)) : Prop :=
  q = 0 ∧ Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) x ∧ Formula.sat domRM x

theorem preM_R (q : ℕ) (x y : State (Var 2)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : PreM q x) : PreM q y := by
  obtain ⟨hq, hg, hd⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · refine (Formula.coincidence _ (fun v hv => ?_)).mp hg
    obtain ⟨i, rfl⟩ := hguardRM 0 (by norm_num) hv
    exact hxy i
  · refine (Formula.coincidence domRM (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRM hv
    exact hxy i

/-- The cover's joint node used: `DRIVE` (the only admissible start; `STALL` is a pruned sink). -/
def J (q : ℕ) : Prop := q = 0
def D (_q : ℕ) : Prop := False

theorem drive_pre (ρ : State (Var 2)) (h : PreM 0 ρ) (T : ℝ) (hT : 0 ≤ T) :
    PreM 0 (driveEnd ρ T) := by
  obtain ⟨-, hg, hd⟩ := h
  rw [sat_guardDRIVE] at hg
  have hsol := drive_sol ρ hd hg.2 T hT
  have he0 := Real.exp_pos (-T)
  have he1 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨rfl, ?_, by simpa [modeM] using hsol.hdom T ⟨hT, le_rfl⟩⟩
  rw [sat_guardDRIVE, driveEnd_R0]
  constructor <;> nlinarith [hg.1, hg.2]

theorem hmoveM (E : ℕ → State (Var 2) → Prop) (hE : ∀ q x, J q → PreM q x → E q x) :
    HMove GrPG modeM J (fun _ => 0) PreM E := by
  intro q hJ ρ hpre T hT
  have hq : q = 0 := hJ
  subst hq
  have hp := drive_pre ρ hpre T hT
  refine Or.inl ⟨fun t => driveEnd ρ t,
    drive_sol ρ hpre.2.2 ((sat_guardDRIVE ρ).mp hpre.2.1).2 T hT, edgeG 0 0,
    List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩, ?_, hE 0 _ rfl hp⟩
  exact hp.2.1

theorem hexitM : HExit GrPG modeM J D (fun _ => 0) PreM PreM := fun _ hD => hD.elim

/-! ## The response to one gated window: the cover's derivation, replayed -/

/-- The window's clocked pieces, less one (`FAST` 3, `MEDIUM` 2, `SLOW` and `RESET` 1). -/
def kOf : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | _ => 0

theorem sat_regionsP0 (x : State (Var 2)) : Formula.sat (regionsP 0) x :=
  sat_sinkRegions_of_lt (by decide) x

theorem not_sat_regionsP1 (x : State (Var 2)) : ¬ Formula.sat (regionsP 1) x := by
  simp [regionsP, sinkRegions, GrM, Formula.sat]

theorem respondR (l : ℕ) (hl : l < 4) (dt : ℝ) (hv : Verd l 0) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM gM gsM) envM) σ)
    (hg : Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) σ) :
    GResp GrPG 0 (gwindowSeg (guardM l) (leftBlock (fLM l)) domLM tgM dt (kOf l + 1))
      (fun qf => Formula.and (Formula.and (FM gM gsM) envM) (regionsP qf)) σ := by
  have hJD : ∀ q, J q ∨ D q → q = 0 := by
    intro q h; rcases h with h | h
    · exact h
    · exact h.elim
  refine replay_gresp GrPG modeM fRM domRM (fLM l) domLM (guardM l) aM
    hgRG (hfLM l hl) hdomLM hdomRM (hguardL l hl) (lamOf l) (lamOf_pos l) J D
    (fun q h => by rw [hJD q h]; exact hfRM 0 (by norm_num)) (fun _ => 0) (fun _ => 0) 1
    (fun _ _ => by norm_num)
    (fun q h => by rw [hJD q h]; exact GrPG_modeAt 0 (by norm_num)) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => by
      have hq : q = 0 := h
      subst hq; exact anc_box l hl hv)
    (fun q h => (h : False).elim)
    (fun q h e he y hA hleg => by
      have hq := hJD q h
      subst hq
      exact hA)
    PreM PreM PreM preM_R preM_R
    (hmoveM _ (fun _ _ _ h => h)) (fun _ _ => hmoveM _ (fun _ _ hJ h => ⟨hJ, h⟩))
    hexitM dt (kOf l) 0 σ ?_ hσ.2.1 _ ?_
  · intro hgL
    refine ⟨Or.inl ⟨rfl, rfl, hg, hσ.2.2⟩, ?_⟩
    exact (anc_iff l hl 0 σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R σ hg⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLM ν :=
      windowSeg_end_domL (leftBlock (fLM l)) domLM tgM dt (kOf l + 1) (by omega) hwin
    have hA' := ((anc_iff l hl q' _).mp hA).1
    have hF : Formula.sat (FM gM gsM) μ := by
      refine (sat_of_agree FMM_fv (fun i => ?_) (fun i => ?_)).mp hA'
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    obtain ⟨hq', -, hdR⟩ := hpre
    subst hq'
    refine ⟨⟨hF, ?_, hdR⟩, sat_regionsP0 μ⟩
    refine (Formula.coincidence domLM (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLM hv
    exact hμL i

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard and `regionsP q`
(`⊤` at `DRIVE`, `⊥` at the pruned sink `STALL`). -/
noncomputable def gregionP (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vsM 2 Side.R (mRM q)) regionsP q

theorem hguardRM_all (q : ℕ) : (hostGuard vsM 2 Side.R (mRM q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsM _ dummyM rfl (by simp [match_multi_rate_IR, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

/-- The left windows, each behind its lowered IR guard (the left automaton's edge test). -/
noncomputable def guardsL : List (Formula (Var 2)) :=
  (List.range 4).map (fun l => hostGuard vsM 2 Side.L (mLM l))

noncomputable def leftDataG : List (Formula (Var 2) × (Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  gatedData guardsL leftDataM

theorem leftDataG_eq : leftDataG =
    [(guardM 0, fLM 0, domLM, 3), (guardM 1, fLM 1, domLM, 2), (guardM 2, fLM 2, domLM, 1),
     (guardM 3, fLM 3, domLM, 1)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 2)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgM dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLM 0 (by norm_num), hdomLM⟩
  · exact ⟨hguardL 1 (by norm_num), hfLM 1 (by norm_num), hdomLM⟩
  · exact ⟨hguardL 2 (by norm_num), hfLM 2 (by norm_num), hdomLM⟩
  · exact ⟨hguardL 3 (by norm_num), hfLM 3 (by norm_num), hdomLM⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvM := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgM dt d.2.2.2 mvM (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`match_multi_rate`, Theorem 3 over the two-mode GUARDED right automaton, the left
windows guard-gated, by replaying the emitted cover** (the choice form; carried to the paper's
left automaton by `theorem3_leftAut_of_choiceR` in `LeftAutLegacy`). At the declared invariant
`v_L ≤ v_R`, both envelopes, the right in the guard of its current mode and never in `STALL`
(`mvRegionR` at `gregionP`). Response (`InstancesV2/BenchCovers/match_multi_rate.lean`): the
right keeps time with window `l` in `DRIVE` (the only admissible start; `STALL` is a pruned
sink, excluded by the region) at the cover's λ (`FAST` 3, `MEDIUM` 2, `SLOW` and `RESET` 1),
the anchor preserved by the joint pack `Verd l 0` (strata `[0]`), and closes with the stay
`DRIVE → DRIVE`, legal since `DRIVE` keeps its guard `0.2 ≤ v_R ≤ 1`. The explicit run gives
only the existence of the right's run. -/
theorem match_multi_rate_guarded (dt : ℝ)
    (h0 : Verd 0 0) (h1 : Verd 1 0) (h2 : Verd 2 0) (h3 : Verd 3 0) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrPG mvM)
      (RFormula.and (RFormula.and (canonInvM gM gsM) (envLR domLM domRM))
        (mvRegionR mvM gregionP GrPG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrPG mvM (FM gM gsM) domLM domRM gregionP
    (leftProgsG dt) (canonInvM gM gsM) (encode_canonInvM gM gsM) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsG, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLG d hd).1
        (hLG d hd).2.1 (hLG d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrPG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrPG mvM (FM gM gsM) envM gregionP (leftProgsG dt)
      hmvFM hmvenvM (fun q => notMem_regionG_fv
        (fun h => aux_notin_range_Rv 0 (hguardRM_all q h)) (notMem_sinkRegions_fv _ q mvM))
      hfreshG (guardsFresh_of_right GrPG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrPG mvM _ regionsP GrPG_guards (FM gM gsM) envM (leftProgsG dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsG, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLG d hd).1
        (hLG d hd).2.1 (hLG d hd).2.2) (hguardRM_all q) hrun
    · intro P hP q hq σ _ hσ hg hreg
      have hq2 : q < 2 := hq
      match q, hq2 with
      | 1, _ => exact absurd hreg (not_sat_regionsP1 σ)
      | 0, _ =>
        simp only [leftProgsG, leftDataG_eq, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hP
        rcases hP with rfl | rfl | rfl | rfl
        · exact respondR 0 (by norm_num) dt h0 hσ hg
        · exact respondR 1 (by norm_num) dt h1 hσ hg
        · exact respondR 2 (by norm_num) dt h2 hσ hg
        · exact respondR 3 (by norm_num) dt h3 hσ hg
  · exact hddF_multiR_G GrPG 0 1 dt leftDataG gregionP (canonInvM gM gsM) domLM domRM
      (by decide) hgRG hRvG hLG
      (fun q _ => regionG_fv_sub (hguardRM_all q) (sinkRegions_fv_sub _ q))
      (canonInvM_varsL gM gsM (by
        intro g' hg'
        simp only [gM, gsM, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gM gsM) hdomLM hdomRM

end MatchMultiRateGuarded
end RelCertifier
