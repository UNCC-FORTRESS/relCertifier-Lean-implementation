/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_chain_rung1`, modal Theorem 3 (switch, per-window λ and k)

The second switch shape: a 3-mode piecewise-rate left envelope (`ApproachFast
θ' = 0.5`, `ApproachSlow θ' = 0.3`, `Return θ' = −0.2`) against the coarse 2-mode
right envelope of the pilot, tolerance `θ_L ≤ θ_R + 0.4`, with PER-WINDOW stretch
and budget: λ = 5/2, k = 3 (Fast); λ = 3/2, k = 2 (Slow); λ = 1, k = 1 (Return).

Every window lands `Approach` (the cover certifies it for all three), so the
pilot's dichotomy transfers with the per-window rate `r_l = λ_l/5`: far anchors
(`θ_R ≤ 1 − r_l·dt`) ride `Approach` alone; near-ceiling anchors take the
drop-tracked B-first split at θ = 1/2 (`cA = cB = r_l`). One variable (`theta`),
padded to `n = 2`; the left fields are constants, so every witness is a line.
dt-capped at 1/5 as in the pilot.

Residuals: three route verdicts (`VerdC l` — the `Approach` coupling per window).
Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.arm_chain_rung1

namespace RelCertifier
namespace ArmChainRung1Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsC : List String := ["theta"]
def dummyC : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLC (l : ℕ) : Parse.PMode := arm_chain_rung1_IR.L.modes.getD l dummyC
def mRC (q : ℕ) : Parse.PMode := arm_chain_rung1_IR.R.modes.getD q dummyC

abbrev mvC : Var 2 := (Side.Aux, 0)
abbrev aC : Fin 2 := (1 : Fin 2)
abbrev tgC : Var 2 := (Side.Aux, aC)

/-- Per-window stretch: `5/2`, `3/2`, `1`. -/
noncomputable def lamC (l : ℕ) : ℝ := if l = 0 then 5/2 else if l = 1 then 3/2 else 1
/-- Per-window λ-stretched right rate `λ_l/5`. -/
noncomputable def rC (l : ℕ) : ℝ := lamC l / 5
/-- Per-window left rate: `1/2`, `3/10`, `−1/5`. -/
noncomputable def rLC (l : ℕ) : ℝ := if l = 0 then 1/2 else if l = 1 then 3/10 else -(1/5)
/-- Per-window budget. -/
def kC (l : ℕ) : ℕ := if l = 0 then 3 else if l = 1 then 2 else 1

theorem lamC_pos (l : ℕ) : 0 < lamC l := by
  unfold lamC
  split <;> [norm_num; skip]
  split <;> norm_num

theorem rC_bounds (l : ℕ) (hl : l < 3) : 1/5 ≤ rC l ∧ rC l ≤ 1/2 := by
  interval_cases l <;> norm_num [rC, lamC]

noncomputable def fLC (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsC 2 Side.L (mLC l)
noncomputable def fRC (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsC 2 Side.R (mRC q)
noncomputable def domLC : Formula (Var 2) := hostEvolve vsC 2 Side.L (mLC 0)
noncomputable def domRC : Formula (Var 2) := hostEvolve vsC 2 Side.R (mRC 0)
noncomputable def envC : Formula (Var 2) := Formula.and domLC domRC

noncomputable def gC : Term (Var 2) :=
  ((Run.invToG vsC 2 ((arm_chain_rung1_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLC_pipe (l : ℕ) (i : Fin 2) : fLC l i =
    (((some (mLC l)).bind (Run.dynOf vsC 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRC_pipe (q : ℕ) (i : Fin 2) : fRC q i =
    (((some (mRC q)).bind (Run.dynOf vsC 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLC_pipe : domLC =
    (((some (mLC 0)).bind (fun m => Run.lowerF vsC 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRC_pipe : domRC =
    (((some (mRC 0)).bind (fun m => Run.lowerF vsC 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLC (l : ℕ) (hl : l < 3) : ∀ i, (fLC l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsC) (some (mLC l))
    (by interval_cases l <;>
      simp [mLC, arm_chain_rung1_IR, Parse.PExpr.namesFree]) i x (fLC_pipe l i ▸ hx))

theorem hfRC (q : ℕ) (hq : q < 2) : ∀ i, (fRC q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsC) (some (mRC q))
    (by interval_cases q <;>
      simp [mRC, arm_chain_rung1_IR, Parse.PExpr.namesFree]) i x (fRC_pipe q i ▸ hx))

theorem hdomLC : domLC.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsC) (some (mLC 0))
    (by simp [mLC, arm_chain_rung1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLC_pipe ▸ hx))

theorem hdomRC : domRC.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsC) (some (mRC 0))
    (by simp [mRC, arm_chain_rung1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRC_pipe ▸ hx))

theorem hgC : gC.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgC : mvC ∉ gC.fv := fun h => by
  rcases hgC h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggC : tgC ∉ gC.fv := fun h => by
  rcases hgC h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvC : mvC ∉ envC.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvC : tgC ∉ envC.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (the REAL λ = 1 automaton) -/

noncomputable def modeC (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRC q) (Term.const 1), dom := domRC, weight := 1 }

def edgeC (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrC : SearchGraph (Var 2) :=
  { modes := [modeC 0, modeC 1],
    edges := [edgeC 0 1, edgeC 0 0, edgeC 1 0, edgeC 1 1] }

theorem GrC_modeAt (q : ℕ) (hq : q < 2) : GrC.modeAt q = some (modeC q) := by
  interval_cases q <;> rfl

theorem httC : ∀ q, ∀ e ∈ GrC.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrC.edges := List.mem_of_mem_filter he
  simp only [GrC, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem hltC : ∀ q, ∀ e ∈ GrC.edgesFrom q, e.tgt < GrC.modes.length := by
  intro q e he
  have hmem : e ∈ GrC.edges := List.mem_of_mem_filter he
  simp only [GrC, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrC, edgeC]

theorem hRvC : ∀ q m, GrC.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeC q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrC])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRC q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRC q) (Term.const 1) (hfRC q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRC hy

theorem edgeC_mem : ∀ st tgt, edgeC st tgt ∈ GrC.edges →
    edgeC st tgt ∈ GrC.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeC]⟩

theorem hfreshC : ∀ q m, GrC.modeAt q = some m →
    mvC ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvC q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family (per-window budgets) -/

noncomputable def leftDataC : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLC 0, domLC, 3), (fLC 1, domLC, 2), (fLC 2, domLC, 1)]

noncomputable def leftProgsC (dt : ℝ) : List (Program (Var 2)) :=
  leftDataC.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgC dt d.2.2)

theorem hLC : ∀ d ∈ leftDataC, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataC, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLC 0 (by norm_num), hdomLC⟩
  · exact ⟨hfLC 1 (by norm_num), hdomLC⟩
  · exact ⟨hfLC 2 (by norm_num), hdomLC⟩

theorem hframesC (dt : ℝ) : ∀ P ∈ leftProgsC dt, FramesMv P mvC := by
  intro P hP
  simp only [leftProgsC, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgC dt d.2.2 mvC (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hc02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hc05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hc03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

theorem fLC0_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fLC l 0) x = rLC l := by
  interval_cases l <;>
    simp [fLC, hostDyn, mLC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc05, hc03, hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, rLC]

theorem fRC0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRC q 0) x = (if q = 0 then (1:ℝ)/5 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRC, hostDyn, mRC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRC1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRC q 1) x = 0 := by
  interval_cases q <;>
    simp [fRC, hostDyn, mRC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domRC (x : State (Var 2)) : Formula.sat domRC x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRC, hostEvolve, mRC, arm_chain_rung1_IR, vsC]
  simp [Run.lowerF, Run.lowerE, hc00, hc10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_domLC (x : State (Var 2)) : Formula.sat domLC x ↔
    (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1) := by
  simp only [domLC, hostEvolve, mLC, arm_chain_rung1_IR, vsC]
  simp [Run.lowerF, Run.lowerE, hc00, hc10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem gC_eval (x : State (Var 2)) :
    Term.eval gC x = x (Lv 0) - (x (Rv 0) + 2/5) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gC, arm_chain_rung1_IR, Run.invToG, Run.lowerE, vsC, hc04,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

/-! ## The split systems (per-window λ) -/

noncomputable def sysXC (l : ℕ) : ODESystem (Var 2) :=
  DLCalTiming.clk tgC (leftBlock (fLC l))
noncomputable def sysBC (l : ℕ) : ODESystem (Var 2) :=
  rightBlock (fRC 1) (Term.const (lamC l))
noncomputable def sysAC (l : ℕ) : ODESystem (Var 2) :=
  rightBlock (fRC 0) (Term.const (lamC l))

theorem hwfXBC (l : ℕ) : (sysXC l ++ sysBC l).WellFormed := by
  show (((sysXC l ++ sysBC l).map Prod.fst)).Nodup
  simp only [sysXC, sysBC, DLCalTiming.clk, leftBlock, rightBlock, List.map_append,
    List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.finRange, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  decide

/-- Two-coordinate affine Lie (copy of the pilot's mirror). -/
theorem lie_affine_coord2 (sys : ODESystem (Var 2)) (hwf : sys.WellFormed)
    (i j : Var 2) (a b c : ℝ) (x : State (Var 2)) :
    Lie sys (fun y => a * y i + b * y j + c) x
      = a * odeField sys x i + b * odeField sys x j := by
  rw [← Lie_eq_fderiv hwf]
  have hpi : HasFDerivAt (fun y : State (Var 2) => y i)
      (ContinuousLinearMap.proj i) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Var 2 => ℝ) i x
  have hpj : HasFDerivAt (fun y : State (Var 2) => y j)
      (ContinuousLinearMap.proj j) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Var 2 => ℝ) j x
  have h1 := ((hpi.const_mul a).add (hpj.const_mul b)).add_const c
  have h1' : HasFDerivAt (fun y : State (Var 2) => a * y i + b * y j + c)
      (a • ContinuousLinearMap.proj i + b • ContinuousLinearMap.proj j) x := h1
  rw [h1'.fderiv]
  simp [ContinuousLinearMap.proj_apply]

theorem memB_Rv0C (l : ℕ) :
    ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 0)) ∈ sysBC l := by
  simp only [sysBC, rightBlock, List.mem_map]
  exact ⟨0, List.mem_finRange 0, rfl⟩

theorem memX_Lv0C (l : ℕ) : ((Lv 0 : Var 2), fLC l 0) ∈ sysXC l := by
  simp only [sysXC, DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map]
  exact Or.inl ⟨0, List.mem_finRange 0, rfl⟩

theorem odeFieldXB_Rv0C (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    odeField (sysXC l ++ sysBC l) x (Rv 0) = -(rC l) := by
  have hmem : ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 0))
      ∈ sysXC l ++ sysBC l := List.mem_append_right _ (memB_Rv0C l)
  have hb : (Rv 0 : Var 2) ∈ (sysXC l ++ sysBC l).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXC l ++ sysBC l) x (Rv 0)
      = ((sysXC l ++ sysBC l).rhs (Rv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Rv 0 : Var 2) = ((Rv 0 : Var 2), Term.binop AOp.mul
      (Term.const (lamC l)) (fRC 1 0)).1 from rfl,
    ODESystem.rhs_eq_of_mem (hwfXBC l) hmem]
  simp only [Term.eval, AOp.interp, fRC0_eval 1 (by norm_num)]
  simp [rC]
  ring

theorem odeFieldXB_Lv0C (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    odeField (sysXC l ++ sysBC l) x (Lv 0) = rLC l := by
  have hmem : ((Lv 0 : Var 2), fLC l 0) ∈ sysXC l ++ sysBC l :=
    List.mem_append_left _ (memX_Lv0C l)
  have hb : (Lv 0 : Var 2) ∈ (sysXC l ++ sysBC l).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXC l ++ sysBC l) x (Lv 0)
      = ((sysXC l ++ sysBC l).rhs (Lv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Lv 0 : Var 2) = ((Lv 0 : Var 2), fLC l 0).1 from rfl,
    ODESystem.rhs_eq_of_mem (hwfXBC l) hmem]
  exact fLC0_eval l hl x

theorem hbndBC (l : ℕ) (hl : l < 3) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLC domRC) x →
    Lie (sysXC l ++ sysBC l) (fun ν => Term.eval gC ν) x ≤ 2 := by
  intro x _
  have hfun : (fun ν : State (Var 2) => Term.eval gC ν)
      = fun y => 1 * y (Lv 0) + (-1) * y (Rv 0) + (-(2/5)) := by
    funext y
    rw [gC_eval]
    ring
  rw [hfun, lie_affine_coord2 _ (hwfXBC l) (Lv 0) (Rv 0) 1 (-1) (-(2/5)) x,
    odeFieldXB_Lv0C l hl, odeFieldXB_Rv0C l hl]
  interval_cases l <;> norm_num [rLC, rC, lamC]

theorem hjrowC (l : ℕ) (hl : l < 3) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLC domRC) x →
    Lie (sysXC l ++ sysBC l) (fun ν => Term.eval (Term.var (Rv 0)) ν) x ≤ -(rC l) := by
  intro x _
  have hfun : (fun ν : State (Var 2) => Term.eval (Term.var (Rv 0)) ν)
      = fun y => 1 * y (Rv 0) + 0 := by
    funext y
    simp [Term.eval]
  rw [hfun, lie_affine_coord _ (hwfXBC l) (Rv 0) 1 0 x, odeFieldXB_Rv0C l hl]
  norm_num

/-! ## Clock-anchored joint box (copy of the pilot's device) -/

theorem box_clk_anchor (g : Term (Var 2)) (A B : ODESystem (Var 2))
    (dom : Formula (Var 2)) (tg : Var 2)
    (htgAb : tg ∉ A.bound) (htgBb : tg ∉ B.bound)
    (htgAr : tg ∉ A.readVars) (htgBr : tg ∉ B.readVars)
    (htgd : tg ∉ dom.fv) (htgg : tg ∉ g.fv) {κ : State (Var 2)}
    (h : Formula.sat (Formula.box (Program.ode (A ++ B) dom) (invLe g)) κ) :
    Formula.sat (Formula.box (Program.ode ((DLCalTiming.clk tg A) ++ B) dom)
      (invLe g)) κ := by
  rw [sat_box] at h ⊢
  intro ω hω
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hω
  have htgrow : ∀ p ∈ A ++ B, tg ∉ p.2.fv := by
    intro p hp htgp
    rcases List.mem_append.mp hp with hp | hp
    · exact htgAr ⟨p, hp, htgp⟩
    · exact htgBr ⟨p, hp, htgp⟩
  have hbnd : ∀ p ∈ A ++ B, p.1 ≠ tg := by
    intro p hp hc
    rcases List.mem_append.mp hp with hp | hp
    · exact htgAb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    · exact htgBb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
  set Ψ : ℝ → State (Var 2) := fun t => Function.update (Φ t) tg (κ tg) with hΨ
  have hΨcoin : ∀ t, ∀ x, x ≠ tg → Ψ t x = Φ t x := by
    intro t x hx
    simp only [hΨ, Function.update_of_ne hx]
  have hrun : Program.sem (Program.ode (A ++ B) dom) κ
      (Function.update ω tg (κ tg)) := by
    refine ⟨r, Ψ, hr, ?_, ?_, ?_, ?_, ?_⟩
    · funext x
      by_cases hx : x = tg
      · subst hx; simp [hΨ, Function.update_self]
      · rw [hΨcoin 0 x hx, hΦ0]
    · funext x
      by_cases hx : x = tg
      · subst hx; simp [hΨ, Function.update_self]
      · rw [hΨcoin r x hx, hΦr, Function.update_of_ne hx]
    · intro t ht p hp
      have hne := hbnd p hp
      have hfun : (fun u => Ψ u p.1) = fun u => Φ u p.1 := by
        funext u
        exact hΨcoin u p.1 hne
      have heval : Term.eval p.2 (Ψ t) = Term.eval p.2 (Φ t) :=
        Term.coincidence p.2 (fun y hy =>
          hΨcoin t y (fun hc => htgrow p hp (by rw [← hc]; exact hy)))
      rw [hfun, heval]
      refine hder t ht p ?_
      simp only [DLCalTiming.clk, List.append_assoc, List.mem_append] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)
    · intro t ht x hx
      by_cases hxtg : x = tg
      · subst hxtg
        simp [hΨ, Function.update_self]
      · rw [hΨcoin t x hxtg]
        refine hmask t ht x ?_
        intro hc
        refine hx ?_
        simp only [ODESystem.bound, List.map_append, List.mem_append] at hc
        simp only [ODESystem.bound, List.map_append, List.mem_append]
        rcases hc with hc | hc
        · left
          have hA : x ∈ List.map Prod.fst (A ++ [(tg, Term.const 1)]) := hc
          rw [List.map_append, List.mem_append] at hA
          rcases hA with h' | h'
          · exact h'
          · exact absurd (by simpa using h') hxtg
        · exact Or.inr hc
    · intro t ht
      refine (Formula.coincidence dom (fun y hy =>
        hΨcoin t y (fun hc => htgd (by rw [← hc]; exact hy)))).mpr (hdom t ht)
  have hinv := h _ hrun
  have hcoin : Term.eval g (Function.update ω tg (κ tg)) = Term.eval g ω :=
    Term.coincidence g (fun y hy =>
      Function.update_of_ne (fun hc => htgg (by rw [← hc]; exact hy)) _ _)
  rw [sat_invLe] at hinv ⊢
  rw [← hcoin]
  exact hinv

/-! ## The route verdicts and the certified `A` box -/

def VerdC (l : ℕ) : Prop :=
  z3solve (flowQuery ⟨gC, fLC l, fRC 0, Term.const (lamC l),
    Formula.and domLC domRC⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gC, fLC l, fRC 0, Term.const (lamC l),
    Formula.and domLC domRC⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gC, fLC l, fRC 0, Term.const (lamC l),
    Formula.and domLC domRC⟩) = Verdict.unsat

theorem hboxAC (l : ℕ) (hl : l < 3) (hv : VerdC l) :
    ∀ κ : State (Var 2), Term.eval gC κ ≤ 0 →
      Formula.sat (Formula.box (Program.ode (sysXC l ++ sysAC l)
        (Formula.and domLC domRC)) (Formula.and (invLe gC) envC)) κ := by
  intro κ hκ
  have hAll := segPresAll_from_strata_verdicts' (fLC l) (fRC 0) (Term.const (lamC l))
    (Formula.and domLC domRC) [gC]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdC] using hv)
  have hjoint : Formula.sat (Formula.box (Program.ode
      (jointSys (fLC l) (fRC 0) (Term.const (lamC l))) (Formula.and domLC domRC))
      (invLe gC)) κ := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll κ ?_ ω hω gC List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hκ
  have htgLb : tgC ∉ (leftBlock (fLC l)).bound := by
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC l) _ h
    exact aux_ne_Lv aC i hi
  have htgAb' : tgC ∉ (rightBlock (fRC 0) (Term.const (lamC l))).bound := by
    intro h
    obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRC 0) (Term.const (lamC l)) _ h
    exact aux_ne_Rv aC i hi
  have htgLr : tgC ∉ (leftBlock (fLC l)).readVars := fun h =>
    aux_notin_range_Lv aC (leftBlock_readVars_sub (fLC l) (hfLC l hl) h)
  have htgAr' : tgC ∉ (rightBlock (fRC 0) (Term.const (lamC l))).readVars := fun h =>
    aux_notin_range_Rv aC (rightBlock_readVars_sub (fRC 0) (Term.const (lamC l))
      (hfRC 0 (by norm_num)) (by simp [Term.fv]) h)
  have htgdom : tgC ∉ (Formula.and domLC domRC).fv := by
    simp only [Formula.fv, Set.mem_union, not_or]
    exact ⟨fun h => aux_notin_range_Lv aC (hdomLC h),
      fun h => aux_notin_range_Rv aC (hdomRC h)⟩
  have hclk := box_clk_anchor gC (leftBlock (fLC l))
    (rightBlock (fRC 0) (Term.const (lamC l))) (Formula.and domLC domRC) tgC
    htgLb htgAb' htgLr htgAr' htgdom htggC
    (by rw [← jointSys_split]; exact hjoint)
  rw [sat_box] at hclk ⊢
  intro ω hω
  refine ⟨hclk ω hω, sem_ode_ends_in_domain hω⟩

/-! ## Rate-generic linear witnesses -/

noncomputable def lineUpR (r : ℝ) (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) + r * t)

noncomputable def lineDnR (r : ℝ) (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) - r * t)

theorem lineUpR_zero (r : ℝ) (base : State (Var 2)) : lineUpR r base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineUpR, Function.update_self]
  · simp [lineUpR, Function.update_of_ne hx]

theorem lineDnR_zero (r : ℝ) (base : State (Var 2)) : lineDnR r base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineDnR, Function.update_self]
  · simp [lineDnR, Function.update_of_ne hx]

theorem lineUpR_run (l : ℕ) (hl : l < 3) (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : 0 ≤ base (Rv 0)) (hhi : base (Rv 0) + rC l * s ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRC 0) (Term.const (lamC l)),
      HasDerivWithinAt (fun u => lineUpR (rC l) base u p.1)
        (p.2.eval (lineUpR (rC l) base t)) (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRC 0) (Term.const (lamC l))).bound →
      lineUpR (rC l) base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRC (lineUpR (rC l) base t)) := by
  have hr0 : 0 ≤ rC l := by
    have := (rC_bounds l hl).1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineUpR (rC l) base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 0 0))
          (lineUpR (rC l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 0 0))
          (lineUpR (rC l) base t) = rC l := by
        simp only [Term.eval, AOp.interp, fRC0_eval 0 (by norm_num)]
        simp [rC]
        ring
      rw [heval]
      have hfun : (fun u => lineUpR (rC l) base u (Rv 0))
          = fun u => base (Rv 0) + rC l * u := by
        funext u
        simp [lineUpR, Function.update_self]
      rw [hfun]
      simpa using (((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul
        (rC l)).const_add (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineUpR (rC l) base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 0 1))
          (lineUpR (rC l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 0 1))
          (lineUpR (rC l) base t) = 0 := by
        simp [Term.eval, AOp.interp, fRC1_eval 0 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineUpR (rC l) base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineUpR, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineUpR, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRC]
    constructor
    · simp only [lineUpR, Function.update_self]
      nlinarith [ht.1]
    · simp only [lineUpR, Function.update_self]
      nlinarith [ht.2]

theorem lineDnR_run (l : ℕ) (hl : l < 3) (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : rC l * s ≤ base (Rv 0)) (hhi : base (Rv 0) ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRC 1) (Term.const (lamC l)),
      HasDerivWithinAt (fun u => lineDnR (rC l) base u p.1)
        (p.2.eval (lineDnR (rC l) base t)) (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRC 1) (Term.const (lamC l))).bound →
      lineDnR (rC l) base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRC (lineDnR (rC l) base t)) := by
  have hr0 : 0 ≤ rC l := by
    have := (rC_bounds l hl).1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineDnR (rC l) base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 0))
          (lineDnR (rC l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 0))
          (lineDnR (rC l) base t) = -(rC l) := by
        simp only [Term.eval, AOp.interp, fRC0_eval 1 (by norm_num)]
        simp [rC]
        ring
      rw [heval]
      have hfun : (fun u => lineDnR (rC l) base u (Rv 0))
          = fun u => base (Rv 0) - rC l * u := by
        funext u
        simp [lineDnR, Function.update_self]
      rw [hfun]
      simpa using (((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul
        (rC l)).const_sub (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineDnR (rC l) base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 1))
          (lineDnR (rC l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamC l)) (fRC 1 1))
          (lineDnR (rC l) base t) = 0 := by
        simp [Term.eval, AOp.interp, fRC1_eval 1 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineDnR (rC l) base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineDnR, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineDnR, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRC]
    constructor
    · simp only [lineDnR, Function.update_self]
      nlinarith [ht.2]
    · simp only [lineDnR, Function.update_self]
      nlinarith [ht.1]

theorem esAloneC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (ω : State (Var 2)) (hω0 : 0 ≤ ω (Rv 0)) (hωfar : ω (Rv 0) ≤ 1 - rC l * dt) :
    HExistSegB (fLC l) (fRC 0) (Term.const (lamC l)) domLC domRC dt ω := by
  intro s ΦL hs0 hsdt hΦL0 hder hmask hdom
  have hr0 : 0 ≤ rC l := by
    have := (rC_bounds l hl).1
    linarith
  have hbase : ΦL s (Rv 0) = ω (Rv 0) := by
    refine hmask s (right_mem_Icc.mpr hs0) (Rv 0) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  obtain ⟨hd, hm, hdm⟩ := lineUpR_run l hl (ΦL s) s hs0
    (by rw [hbase]; exact hω0)
    (by rw [hbase]; nlinarith)
  exact ⟨lineUpR (rC l) (ΦL s), lineUpR_zero (rC l) (ΦL s), hd, hm, hdm⟩

/-! ## The dichotomy coupling (per-window rate) -/

theorem htgXC (l : ℕ) : (tgC, Term.const 1) ∈ sysXC l := by
  show (tgC, Term.const 1) ∈ leftBlock (fLC l) ++ [(tgC, Term.const 1)]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem hRv0notXC (l : ℕ) : (Rv 0 : Var 2) ∉ (sysXC l).bound := by
  intro h
  simp only [sysXC, DLCalTiming.clk, ODESystem.bound, List.map_append,
    List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [tgC, Rv, Prod.ext_iff])

theorem hdisjXRC (l : ℕ) (hl : l < 3) (q : ℕ) (hq : q < 2) :
    Disjoint ((sysXC l).boundSet ∪ (sysXC l).readVars)
      ((rightBlock (fRC q) (Term.const (lamC l))).boundSet
        ∪ (rightBlock (fRC q) (Term.const (lamC l))).readVars) := by
  rw [Set.disjoint_left]
  intro x hxX hxR
  have hxRv : x ∈ range Rv := by
    rcases hxR with h | h
    · exact rightBlock_boundSet_sub (fRC q) (Term.const (lamC l)) h
    · exact rightBlock_readVars_sub (fRC q) (Term.const (lamC l)) (hfRC q hq)
        (by simp [Term.fv]) h
  obtain ⟨i, hi⟩ := hxRv
  rcases hxX with h | h
  · rw [sysXC, clk_boundSet] at h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub (fLC l) h
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hi
      exact absurd hi (by simp [tgC, Rv, Prod.ext_iff])
  · rw [sysXC, clk_readVars] at h
    obtain ⟨j, hj⟩ := leftBlock_readVars_sub (fLC l) (hfLC l hl) h
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem coupleSplitC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (hdt5 : dt ≤ 1/5) (hv : VerdC l) (ω : State (Var 2))
    (hσ : Formula.sat (Formula.and (invLe gC) envC) ω)
    (hnear : 1 - rC l * dt < ω (Rv 0)) :
    faModalB (Equiv.refl (Var 2)) (Program.ode (sysXC l) domLC)
      (Program.seq (Program.ode (sysBC l) domRC) (Program.ode (sysAC l) domRC))
      (Formula.and (invLe gC) envC) tgC dt ω := by
  have hωL := (sat_domLC ω).mp hσ.2.1
  have hωR := (sat_domRC ω).mp hσ.2.2
  have hrb := rC_bounds l hl
  refine faModal_ODE_split_bounded (sysXC l) (sysBC l) (sysAC l)
    domLC domRC domRC (Formula.and (invLe gC) envC)
    gC 2 (by norm_num) (Rv 0) (rC l) (1/2) dt (by norm_num) (by norm_num)
    tgC (htgXC l) (hwfXBC l) (hdisjXRC l hl 1 (by norm_num))
    (hdisjXRC l hl 0 (by norm_num))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ω (hbndBC l hl) (hjrowC l hl) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := hdomLC hx
    subst hi
    exact Or.inl (by rw [sysXC, clk_boundSet]; exact Or.inl (Lv_mem_leftBlock_boundSet _ i))
  · intro x hx
    obtain ⟨i, hi⟩ := hdomRC hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x hx
    obtain ⟨i, hi⟩ := hdomRC hx
    subst hi
    exact Or.inl (Rv_mem_rightBlock_boundSet _ _ i)
  · intro x hx
    rw [sysXC, clk_readVars] at hx
    obtain ⟨i, hi⟩ := leftBlock_readVars_sub (fLC l) (hfLC l hl) hx
    subst hi
    rw [sysXC, clk_boundSet]
    exact Or.inl (Lv_mem_leftBlock_boundSet _ i)
  · intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRC 1) (Term.const (lamC l))
      (hfRC 1 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRC 0) (Term.const (lamC l))
      (hfRC 0 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x
    simp [sysAC, sysBC, rightBlock, ODESystem.bound, List.map_map, Function.comp_def]
  · -- hg0
    have hg := gC_eval ω
    rw [hg]
    nlinarith [hωL.2, hrb.2]
  · intro κ hκ
    exact hboxAC l hl hv κ hκ
  · -- hExistB
    intro s1 ΦL hs10 hs1dt hΦL0 hder hmask hdoms
    have hbase : ΦL s1 (Rv 0) = ω (Rv 0) :=
      hmask s1 (right_mem_Icc.mpr hs10) (Rv 0) (hRv0notXC l)
    obtain ⟨hd, hm, hdm⟩ := lineDnR_run l hl (ΦL s1) s1 hs10
      (by rw [hbase]; nlinarith [hrb.1, hrb.2])
      (by rw [hbase]; exact hωR.2)
    exact ⟨lineDnR (rC l) (ΦL s1), lineDnR_zero (rC l) (ΦL s1), hd, hm, hdm⟩
  · -- hExistA
    intro s1 s2 ΨL κ' hs1 hs2 hs2dt hfr hdrop hΨ0 hΨder hΨmask hΨdom hκ'B hκ'g
    have hs1s2 : s1 = s2 := by linarith
    have hbase : ΨL s2 (Rv 0) = κ' (Rv 0) :=
      hΨmask s2 (right_mem_Icc.mpr hs2) (Rv 0) (hRv0notXC l)
    have hκ'R := (sat_domRC κ').mp hκ'B
    obtain ⟨hd, hm, hdm⟩ := lineUpR_run l hl (ΨL s2) s2 hs2
      (by rw [hbase]; exact hκ'R.1)
      (by rw [hbase]; nlinarith [hωR.2])
    exact ⟨lineUpR (rC l) (ΨL s2), lineUpR_zero (rC l) (ΨL s2), hd, hm, hdm⟩

theorem seqB_of_AC (l : ℕ) : ∀ ν μ : State (Var 2),
    Program.sem (Program.ode (sysAC l) domRC) ν μ →
    Program.sem (Program.seq (Program.ode (sysBC l) domRC)
      (Program.ode (sysAC l) domRC)) ν μ := by
  intro ν μ hA
  have hdomν : Formula.sat domRC ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hA
    have := hdom 0 (left_mem_Icc.mpr hr)
    rwa [hΦ0] at this
  refine ⟨ν, ⟨0, fun _ => ν, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩, hA⟩
  · intro t ht p hp
    have h0 : t = 0 := le_antisymm ht.2 ht.1
    subst h0
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hempty : (Set.Icc (0:ℝ) 0) \ {0} = (∅ : Set ℝ) := by
      simp [Set.Icc_self]
    rw [hempty, nhdsWithin_empty]
    exact Filter.tendsto_bot
  · intro t ht x hx
    rfl
  · intro t ht
    exact hdomν

theorem coupleAloneC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt) (hv : VerdC l)
    (σ' : State (Var 2))
    (hσ' : Formula.sat (Formula.and (invLe gC) envC) σ') (htg0 : σ' tgC = 0)
    (hfar : σ' (Rv 0) ≤ 1 - rC l * dt) :
    faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgC (leftBlock (fLC l))) domLC)
      (Program.ode (rightBlock (fRC 0) (Term.const (lamC l))) domRC)
      (Formula.and (invLe gC) envC) tgC dt σ' := by
  have hupd : Function.update σ' tgC (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgC
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLC l) (fRC 0) (Term.const (lamC l))
    (Formula.and domLC domRC) [gC]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdC] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLC l) ++ rightBlock (fRC 0) (Term.const (lamC l)))
      (Formula.and domLC domRC)) (invLe gC)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gC
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gC σ').mp hσ'.1
  have hωR := (sat_domRC σ').mp hσ'.2.2
  have hES : HExistSegB (fLC l) (fRC 0) (Term.const (lamC l)) domLC domRC dt
      (Function.update σ' tgC 0) := by
    rw [hupd]
    exact esAloneC l hl dt hdt0 σ' hωR.1 hfar
  have hbase := segment_faModalB_from_certB gC (fLC l) (fRC 0) (Term.const (lamC l))
    domLC domRC tgC dt
    (LR_blocks_disjoint _ _ _ (hfLC l hl) (hfRC 0 (by norm_num)) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLC hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRC hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC l) _ h
      exact aux_ne_Lv aC i hi)
    (fun h => aux_notin_range_Lv aC (leftBlock_readVars_sub (fLC l) (hfLC l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRC 0) (Term.const (lamC l)) _ h
      exact aux_ne_Rv aC i hi)
    (fun h => aux_notin_range_Rv aC (rightBlock_readVars_sub (fRC 0)
      (Term.const (lamC l)) (hfRC 0 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aC (rightBlock_boundSet_sub (fRC 0)
      (Term.const (lamC l)) h))
    (fun h => aux_notin_range_Lv aC (hdomLC h))
    (fun h => aux_notin_range_Rv aC (hdomRC h))
    htggC hbox hES
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLC ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRC μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLC μ := by
    rwa [(Formula.coincidence domLC (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLC hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRC 0) (Term.const (lamC l)) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLC μ ↔ Formula.sat domLC ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem coupleC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdC l) :
    ∀ σ', Formula.sat (Formula.and (invLe gC) envC) σ' → σ' tgC = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgC (leftBlock (fLC l))) domLC)
        (Program.seq (Program.ode (rightBlock (fRC 1) (Term.const 1)) domRC)
          (Program.ode (rightBlock (fRC 0) (Term.const 1)) domRC))
        (Formula.and (invLe gC) envC) tgC dt σ' := by
  intro σ' hσ' htg0
  have hstretch : faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgC (leftBlock (fLC l))) domLC)
      (Program.seq (Program.ode (sysBC l) domRC) (Program.ode (sysAC l) domRC))
      (Formula.and (invLe gC) envC) tgC dt σ' := by
    by_cases hc : 1 - rC l * dt < σ' (Rv 0)
    · exact coupleSplitC l hl dt hdt0 hdt5 hv σ' hσ' hc
    · exact faModalB_monoQ (seqB_of_AC l)
        (coupleAloneC l hl dt hdt0 hv σ' hσ' htg0 (by linarith [not_lt.mp hc]))
  refine faModalB_monoQ ?_ hstretch
  intro ν μ hsem
  obtain ⟨κ, hB, hA⟩ := hsem
  exact ⟨κ, sem_rightBlock_reparam (lamC l) 1 (lamC_pos l) one_pos hB,
    sem_rightBlock_reparam (lamC l) 1 (lamC_pos l) one_pos hA⟩

/-! ## Assembly -/

noncomputable def pieceC : Program (Var 2) :=
  Program.seq (Program.ode (rightBlock (fRC 1) (Term.const 1)) domRC)
    (Program.ode (rightBlock (fRC 0) (Term.const 1)) domRC)

theorem coupleC' (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdC l) :
    ∀ σ, Formula.sat (Formula.and (invLe gC) envC) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgC (leftBlock (fLC l))) domLC)
        pieceC (Formula.and (invLe gC) envC) tgC dt
        (Function.update σ tgC 0) := by
  intro σ hσ
  have htgφ : tgC ∉ (Formula.and (invLe gC) envC).fv := by
    intro h
    rcases h with h | h
    · exact htggC (by simpa [invLe, Formula.fv, Term.fv] using h)
    · exact htgenvC h
  have hupdφ : Formula.sat (Formula.and (invLe gC) envC)
      (Function.update σ tgC 0) := by
    rwa [(Formula.coincidence (Formula.and (invLe gC) envC) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (invLe gC) envC) _ ↔ _)]
  exact coupleC l hl dt hdt0 hdt5 hv (Function.update σ tgC 0) hupdφ
    (Function.update_self _ _ _)

theorem hdisPieceC (l : ℕ) (hl : l < 3) (dt : ℝ) :
    Disjoint (Program.vars (pieceC.rename (Equiv.refl (Var 2))))
      (Program.vars (clockedSeg (leftBlock (fLC l)) domLC tgC dt)) := by
  rw [Program.rename_refl, Set.disjoint_left]
  intro x hx hxW
  have hxR : x ∈ range Rv := by
    rcases vars_seq_sub _ _ hx with hx | hx <;>
      · rcases vars_ode_sub _ _ hx with hx | hx
        · rcases hx with hx | hx
          · exact rightBlock_boundSet_sub _ _ hx
          · refine rightBlock_readVars_sub _ (Term.const 1) ?_ (by simp [Term.fv]) hx
            first
              | exact hfRC 1 (by norm_num)
              | exact hfRC 0 (by norm_num)
        · exact hdomRC hx
  rcases vars_clockedSegL_sub (fLC l) domLC aC dt (hfLC l hl) hdomLC hxW with hx' | hx'
  · rw [Set.mem_singleton_iff] at hx'
    obtain ⟨i, hi⟩ := hxR
    rw [hx'] at hi
    exact absurd hi (by simp [Rv, Prod.ext_iff])
  · obtain ⟨i, hi⟩ := hxR
    obtain ⟨j, hj⟩ := hx'
    rw [← hi] at hj
    exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sem_seqPairs : ∀ (k : ℕ) (p q : Program (Var 2)) (ν μ : State (Var 2)),
    Program.sem (bigSeq (List.replicate k (Program.seq p q))) ν μ →
    Program.sem (bigSeq ((List.replicate k [p, q]).flatten)) ν μ := by
  intro k
  induction k with
  | zero => intro p q ν μ h; exact h
  | succ n ih =>
      intro p q ν μ h
      simp only [List.replicate_succ, bigSeq] at h
      obtain ⟨κ, hseq, hrest⟩ := h
      obtain ⟨κ', hp, hq⟩ := hseq
      simp only [List.replicate_succ, List.flatten_cons, List.cons_append,
        List.nil_append, bigSeq]
      exact ⟨κ', hp, κ, hq, ih p q κ μ hrest⟩

theorem segRetC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdC l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (invLe gC) envC) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLC l)) domLC tgC dt (kC l))
      (bigSeq ((List.replicate (kC l)
        [Program.ode (rightBlock (fRC 1) (Term.const 1)) domRC,
         Program.ode (rightBlock (fRC 0) (Term.const 1)) domRC]).flatten))
      (Formula.and (invLe gC) envC)) σ := by
  have hkpos : 0 < kC l := by
    interval_cases l <;> norm_num [kC]
  have hfa := Hmulti_windowR_prefixed (fLC l) domLC gC envC aC dt (kC l) htggC htgenvC
    [] (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfLC l hl) hdomLC
    (List.replicate (kC l) pieceC) (by simp) hkpos
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hdisPieceC l hl dt)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleC' l hl dt hdt0 hdt5 hv σ' hσ')
    hσ
  simp only [List.map_nil, List.nil_append] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_seqPairs (kC l) _ _ ν μ hrun) hfa

theorem segAppC (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdC l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (invLe gC) envC) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLC l)) domLC tgC dt (kC l))
      (bigSeq (Program.ode (rightBlock (fRC 0) (Term.const 1)) domRC ::
        (List.replicate (kC l)
          [Program.ode (rightBlock (fRC 1) (Term.const 1)) domRC,
           Program.ode (rightBlock (fRC 0) (Term.const 1)) domRC]).flatten))
      (Formula.and (invLe gC) envC)) σ := by
  have hkpos : 0 < kC l := by
    interval_cases l <;> norm_num [kC]
  have hfa := Hmulti_windowR_prefixed (fLC l) domLC gC envC aC dt (kC l) htggC htgenvC
    [⟨fRC 0, Term.const 1, domRC⟩]
    (by
      intro h hh
      rw [List.mem_singleton] at hh
      subst hh
      exact ⟨hfRC 0 (by norm_num), by simp [Term.fv], hdomRC⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' htg'
      rw [List.mem_singleton] at hh
      subst hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fRC 0)
        (lam := Term.const 1) (domR := domRC) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfLC l hl) hdomLC
    (List.replicate (kC l) pieceC) (by simp) hkpos
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hdisPieceC l hl dt)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleC' l hl dt hdt0 hdt5 hv σ' hσ')
    hσ
  refine sat_faModal_monoR (fun ν μ hrun => ?_) hfa
  simp only [List.map_cons, List.map_nil, List.singleton_append, bigSeq] at hrun ⊢
  obtain ⟨κ, hhop, hrest⟩ := hrun
  exact ⟨κ, hhop, sem_seqPairs (kC l) _ _ κ μ hrest⟩

theorem HmultiC (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdC 0) (hv1 : VerdC 1) (hv2 : VerdC 2) :
    ∀ P ∈ leftProgsC dt, ∀ (q : ℕ), q < GrC.modes.length → ∀ σ, σ mvC = (q : ℝ) →
      Formula.sat (Formula.and (invLe gC) envC) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrC.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrC.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gC) envC)) σ := by
  intro P hP q hq σ hmv hσ
  have hq2 : q < 2 := by simpa [GrC] using hq
  have hsingle : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2))
      (b : ℕ × RMode (Var 2) × REdge (Var 2)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halignseg : ∀ s ∈ [((1:ℕ), modeC 1, edgeC 1 0), ((0:ℕ), modeC 0, edgeC 0 1),
      ((1:ℕ), modeC 1, edgeC 1 0), ((0:ℕ), modeC 0, edgeC 0 1),
      ((1:ℕ), modeC 1, edgeC 1 0), ((0:ℕ), modeC 0, edgeC 0 0)],
      GrC.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrC.edgesFrom s.1 := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨GrC_modeAt 0 (by norm_num), edgeC_mem 0 1 (by simp [GrC])⟩
        | exact ⟨GrC_modeAt 0 (by norm_num), edgeC_mem 0 0 (by simp [GrC])⟩
        | exact ⟨GrC_modeAt 1 (by norm_num), edgeC_mem 1 0 (by simp [GrC])⟩
  have halignhop : GrC.modeAt 0 = some (modeC 0) ∧ edgeC 0 1 ∈ GrC.edgesFrom 0 :=
    ⟨GrC_modeAt 0 (by norm_num), edgeC_mem 0 1 (by simp [GrC])⟩
  simp only [leftProgsC, leftDataC, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  all_goals interval_cases q
  -- window Fast (k = 3), start Approach
  · refine ⟨(0, modeC 0, edgeC 0 1) ::
      [(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      (by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact halignhop
        · exact halignseg s hs),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)))))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segAppC 0 (by norm_num) dt hdt0 hdt5 hv0 hσ
    simpa [modeC, kC, List.replicate] using this
  -- window Fast, start Return
  · refine ⟨[(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      halignseg,
      hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hsingle _))))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segRetC 0 (by norm_num) dt hdt0 hdt5 hv0 hσ
    simpa [modeC, kC, List.replicate] using this
  -- window Slow (k = 2), start Approach
  · refine ⟨(0, modeC 0, edgeC 0 1) ::
      [(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      (by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact halignhop
        · refine halignseg s ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
          tauto),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hsingle _)))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segAppC 1 (by norm_num) dt hdt0 hdt5 hv1 hσ
    simpa [modeC, kC, List.replicate] using this
  -- window Slow, start Return
  · refine ⟨[(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 1),
       (1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      (by
        intro s hs
        refine halignseg s ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        tauto),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segRetC 1 (by norm_num) dt hdt0 hdt5 hv1 hσ
    simpa [modeC, kC, List.replicate] using this
  -- window Return (k = 1), start Approach
  · refine ⟨(0, modeC 0, edgeC 0 1) ::
      [(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      (by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact halignhop
        · refine halignseg s ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
          tauto),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segAppC 2 (by norm_num) dt hdt0 hdt5 hv2 hσ
    simpa [modeC, kC, List.replicate] using this
  -- window Return, start Return
  · refine ⟨[(1, modeC 1, edgeC 1 0), (0, modeC 0, edgeC 0 0)],
      (by
        intro s hs
        refine halignseg s ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        tauto),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      ?_⟩
    have := segRetC 2 (by norm_num) dt hdt0 hdt5 hv2 hσ
    simpa [modeC, kC, List.replicate] using this

/-- **`arm_chain_rung1`, modal Theorem 3** — the per-window λ/k switch instance. -/
theorem arm_chain_rung1_modal (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdC 0) (hv1 : VerdC 1) (hv2 : VerdC 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsC dt))
      (rightAutomatonBody GrC mvC)
      (RFormula.and (RFormula.and (canonInv gC) (envLR domLC domRC))
        (mvValidR mvC GrC.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrC mvC gC domLC domRC (leftProgsC dt)
    (canonInv gC) (encode_canonInv gC) ?_ ?_ ?_
  · exact hdis_multi GrC 0 1 dt leftDataC (by decide) httC hRvC hLC
  · exact hstep_assembled_multiE GrC mvC gC envC (leftProgsC dt) hmvgC hmvenvC
      hfreshC httC hltC (hframesC dt)
      (HmultiC dt hdt0 hdt5 hv0 hv1 hv2)
  · exact hddF_multiE GrC 0 1 dt leftDataC (canonInv gC) domLC domRC (by decide)
      httC hRvC hLC (canonInv_varsL gC hgC) (canonInv_varsR gC) hdomLC hdomRC

end ArmChainRung1Modal
end RelCertifier