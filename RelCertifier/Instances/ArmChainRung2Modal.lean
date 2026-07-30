/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_chain_rung2`, modal Theorem 3 (the asymmetric-rate switch)

The last switch benchmark: the 4-mode Hold-terminating left envelope
(0.5 / 0.35 / 0.2 / 0) against the 3-mode right envelope (Fast 0.5 / Slow 0.3 /
Return −0.2), tolerance `θ_L ≤ θ_R + 0.30`, per-window stretch λ = 7/4, 5/4, 1, 1
and budgets k = 2, 2, 1, 1. Every window lands `ApproachSlow`.

The split here is ASYMMETRIC: the landing rate `cA = 0.3·λ` differs from the
Return rate `cB = 0.2·λ`, so the B-first fraction is `θ = 3/5` — then
`s₂ = (2/3)·s₁` and the rise `cA·s₂ = cB·s₁` cancels the drop exactly. The
pre-L3′ measurement needed a banded θ-family here; under the drop-tracked split
the single fraction closes all four windows at `dt ≤ 1/5` (worst budget
1.125·dt ≤ 0.225 < 0.3, in-kernel).

Residuals: four route verdicts (`VerdD l` — the `ApproachSlow` coupling per
window). Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.arm_chain_rung2

namespace RelCertifier
namespace ArmChainRung2Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsD : List String := ["theta"]
def dummyD : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLD (l : ℕ) : Parse.PMode := arm_chain_rung2_IR.L.modes.getD l dummyD
def mRD (q : ℕ) : Parse.PMode := arm_chain_rung2_IR.R.modes.getD q dummyD

abbrev mvD : Var 2 := (Side.Aux, 0)
abbrev aD : Fin 2 := (1 : Fin 2)
abbrev tgD : Var 2 := (Side.Aux, aD)

/-- Per-window stretch: `7/4`, `5/4`, `1`, `1`. -/
noncomputable def lamD (l : ℕ) : ℝ :=
  if l = 0 then 7/4 else if l = 1 then 5/4 else 1
/-- Landing (`ApproachSlow`) λ-stretched rate `0.3·λ`. -/
noncomputable def cAD (l : ℕ) : ℝ := 3/10 * lamD l
/-- `Return` λ-stretched rate `0.2·λ`. -/
noncomputable def cBD (l : ℕ) : ℝ := 1/5 * lamD l
/-- Per-window left rate: `1/2`, `7/20`, `1/5`, `0`. -/
noncomputable def rLD (l : ℕ) : ℝ :=
  if l = 0 then 1/2 else if l = 1 then 7/20 else if l = 2 then 1/5 else 0
/-- Per-window budget. -/
def kD (l : ℕ) : ℕ := if l ≤ 1 then 2 else 1

theorem lamD_pos (l : ℕ) : 0 < lamD l := by
  unfold lamD
  split <;> [norm_num; skip]
  split <;> norm_num

theorem lamD_bounds (l : ℕ) (hl : l < 4) : 1 ≤ lamD l ∧ lamD l ≤ 7/4 := by
  interval_cases l <;> norm_num [lamD]

noncomputable def fLD (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.L (mLD l)
noncomputable def fRD (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.R (mRD q)
noncomputable def domLD : Formula (Var 2) := hostEvolve vsD 2 Side.L (mLD 0)
noncomputable def domRD : Formula (Var 2) := hostEvolve vsD 2 Side.R (mRD 0)
noncomputable def envD : Formula (Var 2) := Formula.and domLD domRD

noncomputable def gD : Term (Var 2) :=
  ((Run.invToG vsD 2 ((arm_chain_rung2_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLD_pipe (l : ℕ) (i : Fin 2) : fLD l i =
    (((some (mLD l)).bind (Run.dynOf vsD 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRD_pipe (q : ℕ) (i : Fin 2) : fRD q i =
    (((some (mRD q)).bind (Run.dynOf vsD 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLD_pipe : domLD =
    (((some (mLD 0)).bind (fun m => Run.lowerF vsD 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRD_pipe : domRD =
    (((some (mRD 0)).bind (fun m => Run.lowerF vsD 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLD (l : ℕ) (hl : l < 4) : ∀ i, (fLD l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsD) (some (mLD l))
    (by interval_cases l <;>
      simp [mLD, arm_chain_rung2_IR, Parse.PExpr.namesFree]) i x (fLD_pipe l i ▸ hx))

theorem hfRD (q : ℕ) (hq : q < 3) : ∀ i, (fRD q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsD) (some (mRD q))
    (by interval_cases q <;>
      simp [mRD, arm_chain_rung2_IR, Parse.PExpr.namesFree]) i x (fRD_pipe q i ▸ hx))

theorem hdomLD : domLD.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsD) (some (mLD 0))
    (by simp [mLD, arm_chain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLD_pipe ▸ hx))

theorem hdomRD : domRD.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsD) (some (mRD 0))
    (by simp [mRD, arm_chain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRD_pipe ▸ hx))

theorem hgD : gD.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgD : mvD ∉ gD.fv := fun h => by
  rcases hgD h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggD : tgD ∉ gD.fv := fun h => by
  rcases hgD h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvD : mvD ∉ envD.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvD : tgD ∉ envD.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph -/

noncomputable def modeD (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRD q) (Term.const 1), dom := domRD, weight := 1 }

def edgeD (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrD : SearchGraph (Var 2) :=
  { modes := [modeD 0, modeD 1, modeD 2],
    edges := [edgeD 0 1, edgeD 0 0, edgeD 1 2, edgeD 1 1, edgeD 2 1, edgeD 2 2] }

theorem GrD_modeAt (q : ℕ) (hq : q < 3) : GrD.modeAt q = some (modeD q) := by
  interval_cases q <;> rfl

theorem httD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.tgt < GrD.modes.length := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [GrD, edgeD]

theorem hRvD : ∀ q m, GrD.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeD q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrD])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRD q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRD q) (Term.const 1) (hfRD q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRD hy

theorem edgeD_mem : ∀ st tgt, edgeD st tgt ∈ GrD.edges →
    edgeD st tgt ∈ GrD.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeD]⟩

theorem hfreshD : ∀ q m, GrD.modeAt q = some m →
    mvD ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvD q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataD : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLD 0, domLD, 2), (fLD 1, domLD, 2), (fLD 2, domLD, 1), (fLD 3, domLD, 1)]

noncomputable def leftProgsD (dt : ℝ) : List (Program (Var 2)) :=
  leftDataD.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgD dt d.2.2)

theorem hLD : ∀ d ∈ leftDataD, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataD, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨hfLD 0 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 1 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 2 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 3 (by norm_num), hdomLD⟩

theorem hframesD (dt : ℝ) : ∀ P ∈ leftProgsD dt, FramesMv P mvD := by
  intro P hP
  simp only [leftProgsD, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgD dt d.2.2 mvD (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins and field/shape pins -/

theorem hd02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd035 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fLD0_eval (l : ℕ) (hl : l < 4) (x : State (Var 2)) :
    Term.eval (fLD l 0) x = rLD l := by
  interval_cases l <;>
    simp [fLD, hostDyn, mLD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd035, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, rLD]

theorem fRD0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fRD q 0) x =
      (if q = 0 then (1:ℝ)/2 else if q = 1 then 3/10 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRD, hostDyn, mRD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd03, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRD1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fRD q 1) x = 0 := by
  interval_cases q <;>
    simp [fRD, hostDyn, mRD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd03, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRD (x : State (Var 2)) : Formula.sat domRD x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRD, hostEvolve, mRD, arm_chain_rung2_IR, vsD]
  simp [Run.lowerF, Run.lowerE, hd00, hd10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_domLD (x : State (Var 2)) : Formula.sat domLD x ↔
    (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1) := by
  simp only [domLD, hostEvolve, mLD, arm_chain_rung2_IR, vsD]
  simp [Run.lowerF, Run.lowerE, hd00, hd10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem gD_eval (x : State (Var 2)) :
    Term.eval gD x = x (Lv 0) - (x (Rv 0) + 3/10) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gD, arm_chain_rung2_IR, Run.invToG, Run.lowerE, vsD, hd030,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

/-! ## The split systems (B = `Return`, A = `ApproachSlow`, per-window λ) -/

noncomputable def sysXD (l : ℕ) : ODESystem (Var 2) :=
  DLCalTiming.clk tgD (leftBlock (fLD l))
noncomputable def sysBD (l : ℕ) : ODESystem (Var 2) :=
  rightBlock (fRD 2) (Term.const (lamD l))
noncomputable def sysAD (l : ℕ) : ODESystem (Var 2) :=
  rightBlock (fRD 1) (Term.const (lamD l))

theorem hwfXBD (l : ℕ) : (sysXD l ++ sysBD l).WellFormed := by
  show (((sysXD l ++ sysBD l).map Prod.fst)).Nodup
  simp only [sysXD, sysBD, DLCalTiming.clk, leftBlock, rightBlock, List.map_append,
    List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.finRange, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  decide

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

theorem memB_Rv0D (l : ℕ) :
    ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 0)) ∈ sysBD l := by
  simp only [sysBD, rightBlock, List.mem_map]
  exact ⟨0, List.mem_finRange 0, rfl⟩

theorem memX_Lv0D (l : ℕ) : ((Lv 0 : Var 2), fLD l 0) ∈ sysXD l := by
  simp only [sysXD, DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map]
  exact Or.inl ⟨0, List.mem_finRange 0, rfl⟩

theorem odeFieldXB_Rv0D (l : ℕ) (hl : l < 4) (x : State (Var 2)) :
    odeField (sysXD l ++ sysBD l) x (Rv 0) = -(cBD l) := by
  have hmem : ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 0))
      ∈ sysXD l ++ sysBD l := List.mem_append_right _ (memB_Rv0D l)
  have hb : (Rv 0 : Var 2) ∈ (sysXD l ++ sysBD l).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXD l ++ sysBD l) x (Rv 0)
      = ((sysXD l ++ sysBD l).rhs (Rv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Rv 0 : Var 2) = ((Rv 0 : Var 2), Term.binop AOp.mul
      (Term.const (lamD l)) (fRD 2 0)).1 from rfl,
    ODESystem.rhs_eq_of_mem (hwfXBD l) hmem]
  simp only [Term.eval, AOp.interp, fRD0_eval 2 (by norm_num)]
  simp [cBD]
  ring

theorem odeFieldXB_Lv0D (l : ℕ) (hl : l < 4) (x : State (Var 2)) :
    odeField (sysXD l ++ sysBD l) x (Lv 0) = rLD l := by
  have hmem : ((Lv 0 : Var 2), fLD l 0) ∈ sysXD l ++ sysBD l :=
    List.mem_append_left _ (memX_Lv0D l)
  have hb : (Lv 0 : Var 2) ∈ (sysXD l ++ sysBD l).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXD l ++ sysBD l) x (Lv 0)
      = ((sysXD l ++ sysBD l).rhs (Lv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Lv 0 : Var 2) = ((Lv 0 : Var 2), fLD l 0).1 from rfl,
    ODESystem.rhs_eq_of_mem (hwfXBD l) hmem]
  exact fLD0_eval l hl x

theorem hbndBD (l : ℕ) (hl : l < 4) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLD domRD) x →
    Lie (sysXD l ++ sysBD l) (fun ν => Term.eval gD ν) x ≤ 1 := by
  intro x _
  have hfun : (fun ν : State (Var 2) => Term.eval gD ν)
      = fun y => 1 * y (Lv 0) + (-1) * y (Rv 0) + (-(3/10)) := by
    funext y
    rw [gD_eval]
    ring
  rw [hfun, lie_affine_coord2 _ (hwfXBD l) (Lv 0) (Rv 0) 1 (-1) (-(3/10)) x,
    odeFieldXB_Lv0D l hl, odeFieldXB_Rv0D l hl]
  interval_cases l <;> norm_num [rLD, cBD, lamD]

theorem hjrowD (l : ℕ) (hl : l < 4) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLD domRD) x →
    Lie (sysXD l ++ sysBD l) (fun ν => Term.eval (Term.var (Rv 0)) ν) x ≤ -(cBD l) := by
  intro x _
  have hfun : (fun ν : State (Var 2) => Term.eval (Term.var (Rv 0)) ν)
      = fun y => 1 * y (Rv 0) + 0 := by
    funext y
    simp [Term.eval]
  rw [hfun, lie_affine_coord _ (hwfXBD l) (Rv 0) 1 0 x, odeFieldXB_Rv0D l hl]
  norm_num

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

def VerdD (l : ℕ) : Prop :=
  z3solve (flowQuery ⟨gD, fLD l, fRD 1, Term.const (lamD l),
    Formula.and domLD domRD⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gD, fLD l, fRD 1, Term.const (lamD l),
    Formula.and domLD domRD⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gD, fLD l, fRD 1, Term.const (lamD l),
    Formula.and domLD domRD⟩) = Verdict.unsat

theorem hboxAD (l : ℕ) (hl : l < 4) (hv : VerdD l) :
    ∀ κ : State (Var 2), Term.eval gD κ ≤ 0 →
      Formula.sat (Formula.box (Program.ode (sysXD l ++ sysAD l)
        (Formula.and domLD domRD)) (Formula.and (invLe gD) envD)) κ := by
  intro κ hκ
  have hAll := segPresAll_from_strata_verdicts' (fLD l) (fRD 1) (Term.const (lamD l))
    (Formula.and domLD domRD) [gD]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdD] using hv)
  have hjoint : Formula.sat (Formula.box (Program.ode
      (jointSys (fLD l) (fRD 1) (Term.const (lamD l))) (Formula.and domLD domRD))
      (invLe gD)) κ := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll κ ?_ ω hω gD List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hκ
  have htgLb : tgD ∉ (leftBlock (fLD l)).bound := by
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD l) _ h
    exact aux_ne_Lv aD i hi
  have htgAb' : tgD ∉ (rightBlock (fRD 1) (Term.const (lamD l))).bound := by
    intro h
    obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRD 1) (Term.const (lamD l)) _ h
    exact aux_ne_Rv aD i hi
  have htgLr : tgD ∉ (leftBlock (fLD l)).readVars := fun h =>
    aux_notin_range_Lv aD (leftBlock_readVars_sub (fLD l) (hfLD l hl) h)
  have htgAr' : tgD ∉ (rightBlock (fRD 1) (Term.const (lamD l))).readVars := fun h =>
    aux_notin_range_Rv aD (rightBlock_readVars_sub (fRD 1) (Term.const (lamD l))
      (hfRD 1 (by norm_num)) (by simp [Term.fv]) h)
  have htgdom : tgD ∉ (Formula.and domLD domRD).fv := by
    simp only [Formula.fv, Set.mem_union, not_or]
    exact ⟨fun h => aux_notin_range_Lv aD (hdomLD h),
      fun h => aux_notin_range_Rv aD (hdomRD h)⟩
  have hclk := box_clk_anchor gD (leftBlock (fLD l))
    (rightBlock (fRD 1) (Term.const (lamD l))) (Formula.and domLD domRD) tgD
    htgLb htgAb' htgLr htgAr' htgdom htggD
    (by rw [← jointSys_split]; exact hjoint)
  rw [sat_box] at hclk ⊢
  intro ω hω
  refine ⟨hclk ω hω, sem_ode_ends_in_domain hω⟩

/-! ## Rate-generic witnesses at the asymmetric rates -/

noncomputable def lineUpD (r : ℝ) (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) + r * t)

noncomputable def lineDnD (r : ℝ) (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) - r * t)

theorem lineUpD_zero (r : ℝ) (base : State (Var 2)) : lineUpD r base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineUpD, Function.update_self]
  · simp [lineUpD, Function.update_of_ne hx]

theorem lineDnD_zero (r : ℝ) (base : State (Var 2)) : lineDnD r base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineDnD, Function.update_self]
  · simp [lineDnD, Function.update_of_ne hx]

theorem cD_bounds (l : ℕ) (hl : l < 4) :
    3/10 ≤ cAD l ∧ cAD l ≤ 21/40 ∧ 1/5 ≤ cBD l ∧ cBD l ≤ 7/20 := by
  interval_cases l <;> norm_num [cAD, cBD, lamD]

theorem lineUpD_run (l : ℕ) (hl : l < 4) (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : 0 ≤ base (Rv 0)) (hhi : base (Rv 0) + cAD l * s ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRD 1) (Term.const (lamD l)),
      HasDerivWithinAt (fun u => lineUpD (cAD l) base u p.1)
        (p.2.eval (lineUpD (cAD l) base t)) (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRD 1) (Term.const (lamD l))).bound →
      lineUpD (cAD l) base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRD (lineUpD (cAD l) base t)) := by
  have hr0 : 0 ≤ cAD l := by
    have := (cD_bounds l hl).1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineUpD (cAD l) base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 1 0))
          (lineUpD (cAD l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 1 0))
          (lineUpD (cAD l) base t) = cAD l := by
        simp only [Term.eval, AOp.interp, fRD0_eval 1 (by norm_num)]
        simp [cAD]
        ring
      rw [heval]
      have hfun : (fun u => lineUpD (cAD l) base u (Rv 0))
          = fun u => base (Rv 0) + cAD l * u := by
        funext u
        simp [lineUpD, Function.update_self]
      rw [hfun]
      simpa using (((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul
        (cAD l)).const_add (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineUpD (cAD l) base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 1 1))
          (lineUpD (cAD l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 1 1))
          (lineUpD (cAD l) base t) = 0 := by
        simp [Term.eval, AOp.interp, fRD1_eval 1 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineUpD (cAD l) base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineUpD, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineUpD, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRD]
    constructor
    · simp only [lineUpD, Function.update_self]
      nlinarith [ht.1]
    · simp only [lineUpD, Function.update_self]
      nlinarith [ht.2]

theorem lineDnD_run (l : ℕ) (hl : l < 4) (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : cBD l * s ≤ base (Rv 0)) (hhi : base (Rv 0) ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRD 2) (Term.const (lamD l)),
      HasDerivWithinAt (fun u => lineDnD (cBD l) base u p.1)
        (p.2.eval (lineDnD (cBD l) base t)) (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRD 2) (Term.const (lamD l))).bound →
      lineDnD (cBD l) base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRD (lineDnD (cBD l) base t)) := by
  have hr0 : 0 ≤ cBD l := by
    have := (cD_bounds l hl).2.2.1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineDnD (cBD l) base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 0))
          (lineDnD (cBD l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 0))
          (lineDnD (cBD l) base t) = -(cBD l) := by
        simp only [Term.eval, AOp.interp, fRD0_eval 2 (by norm_num)]
        simp [cBD]
        ring
      rw [heval]
      have hfun : (fun u => lineDnD (cBD l) base u (Rv 0))
          = fun u => base (Rv 0) - cBD l * u := by
        funext u
        simp [lineDnD, Function.update_self]
      rw [hfun]
      simpa using (((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul
        (cBD l)).const_sub (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineDnD (cBD l) base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 1))
          (lineDnD (cBD l) base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const (lamD l)) (fRD 2 1))
          (lineDnD (cBD l) base t) = 0 := by
        simp [Term.eval, AOp.interp, fRD1_eval 2 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineDnD (cBD l) base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineDnD, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineDnD, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRD]
    constructor
    · simp only [lineDnD, Function.update_self]
      nlinarith [ht.2]
    · simp only [lineDnD, Function.update_self]
      nlinarith [ht.1]

theorem esAloneD (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (ω : State (Var 2)) (hω0 : 0 ≤ ω (Rv 0)) (hωfar : ω (Rv 0) ≤ 1 - cAD l * dt) :
    HExistSegB (fLD l) (fRD 1) (Term.const (lamD l)) domLD domRD dt ω := by
  intro s ΦL hs0 hsdt hΦL0 hder hmask hdom
  have hr0 : 0 ≤ cAD l := by
    have := (cD_bounds l hl).1
    linarith
  have hbase : ΦL s (Rv 0) = ω (Rv 0) := by
    refine hmask s (right_mem_Icc.mpr hs0) (Rv 0) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  obtain ⟨hd, hm, hdm⟩ := lineUpD_run l hl (ΦL s) s hs0
    (by rw [hbase]; exact hω0)
    (by rw [hbase]; nlinarith)
  exact ⟨lineUpD (cAD l) (ΦL s), lineUpD_zero (cAD l) (ΦL s), hd, hm, hdm⟩

/-! ## The θ = 3/5 dichotomy coupling -/

theorem htgXD (l : ℕ) : (tgD, Term.const 1) ∈ sysXD l := by
  show (tgD, Term.const 1) ∈ leftBlock (fLD l) ++ [(tgD, Term.const 1)]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem hRv0notXD (l : ℕ) : (Rv 0 : Var 2) ∉ (sysXD l).bound := by
  intro h
  simp only [sysXD, DLCalTiming.clk, ODESystem.bound, List.map_append,
    List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [tgD, Rv, Prod.ext_iff])

theorem hdisjXRD (l : ℕ) (hl : l < 4) (q : ℕ) (hq : q < 3) :
    Disjoint ((sysXD l).boundSet ∪ (sysXD l).readVars)
      ((rightBlock (fRD q) (Term.const (lamD l))).boundSet
        ∪ (rightBlock (fRD q) (Term.const (lamD l))).readVars) := by
  rw [Set.disjoint_left]
  intro x hxX hxR
  have hxRv : x ∈ range Rv := by
    rcases hxR with h | h
    · exact rightBlock_boundSet_sub (fRD q) (Term.const (lamD l)) h
    · exact rightBlock_readVars_sub (fRD q) (Term.const (lamD l)) (hfRD q hq)
        (by simp [Term.fv]) h
  obtain ⟨i, hi⟩ := hxRv
  rcases hxX with h | h
  · rw [sysXD, clk_boundSet] at h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub (fLD l) h
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hi
      exact absurd hi (by simp [tgD, Rv, Prod.ext_iff])
  · rw [sysXD, clk_readVars] at h
    obtain ⟨j, hj⟩ := leftBlock_readVars_sub (fLD l) (hfLD l hl) h
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem coupleSplitD (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (hdt5 : dt ≤ 1/5) (hv : VerdD l) (ω : State (Var 2))
    (hσ : Formula.sat (Formula.and (invLe gD) envD) ω)
    (hnear : 1 - cAD l * dt < ω (Rv 0)) :
    faModalB (Equiv.refl (Var 2)) (Program.ode (sysXD l) domLD)
      (Program.seq (Program.ode (sysBD l) domRD) (Program.ode (sysAD l) domRD))
      (Formula.and (invLe gD) envD) tgD dt ω := by
  have hωL := (sat_domLD ω).mp hσ.2.1
  have hωR := (sat_domRD ω).mp hσ.2.2
  have hcb := cD_bounds l hl
  refine faModal_ODE_split_bounded (sysXD l) (sysBD l) (sysAD l)
    domLD domRD domRD (Formula.and (invLe gD) envD)
    gD 1 (by norm_num) (Rv 0) (cBD l) (3/5) dt (by norm_num) (by norm_num)
    tgD (htgXD l) (hwfXBD l) (hdisjXRD l hl 2 (by norm_num))
    (hdisjXRD l hl 1 (by norm_num))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ω (hbndBD l hl) (hjrowD l hl) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := hdomLD hx
    subst hi
    exact Or.inl (by rw [sysXD, clk_boundSet]; exact Or.inl (Lv_mem_leftBlock_boundSet _ i))
  · intro x hx
    obtain ⟨i, hi⟩ := hdomRD hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x hx
    obtain ⟨i, hi⟩ := hdomRD hx
    subst hi
    exact Or.inl (Rv_mem_rightBlock_boundSet _ _ i)
  · intro x hx
    rw [sysXD, clk_readVars] at hx
    obtain ⟨i, hi⟩ := leftBlock_readVars_sub (fLD l) (hfLD l hl) hx
    subst hi
    rw [sysXD, clk_boundSet]
    exact Or.inl (Lv_mem_leftBlock_boundSet _ i)
  · intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRD 2) (Term.const (lamD l))
      (hfRD 2 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRD 1) (Term.const (lamD l))
      (hfRD 1 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · intro x
    simp [sysAD, sysBD, rightBlock, ODESystem.bound, List.map_map, Function.comp_def]
  · -- hg0: the near-ceiling budget at θ = 3/5, MgB = 1
    have hg := gD_eval ω
    rw [hg]
    nlinarith [hωL.2, hcb.2.1]
  · intro κ hκ
    exact hboxAD l hl hv κ hκ
  · -- hExistB: the falling Return line
    intro s1 ΦL hs10 hs1dt hΦL0 hder hmask hdoms
    have hbase : ΦL s1 (Rv 0) = ω (Rv 0) :=
      hmask s1 (right_mem_Icc.mpr hs10) (Rv 0) (hRv0notXD l)
    obtain ⟨hd, hm, hdm⟩ := lineDnD_run l hl (ΦL s1) s1 hs10
      (by rw [hbase]; nlinarith [hcb.2.1, hcb.2.2.2])
      (by rw [hbase]; exact hωR.2)
    exact ⟨lineDnD (cBD l) (ΦL s1), lineDnD_zero (cBD l) (ΦL s1), hd, hm, hdm⟩
  · -- hExistA: the rising Slow line; the asymmetric fraction cancels the drop
    intro s1 s2 ΨL κ' hs1 hs2 hs2dt hfr hdrop hΨ0 hΨder hΨmask hΨdom hκ'B hκ'g
    have h32 : 3 * s2 = 2 * s1 := by linarith
    have hcs : cAD l * s2 = cBD l * s1 := by
      simp only [cAD, cBD]
      linear_combination (lamD l / 10) * h32
    have hbase : ΨL s2 (Rv 0) = κ' (Rv 0) :=
      hΨmask s2 (right_mem_Icc.mpr hs2) (Rv 0) (hRv0notXD l)
    have hκ'R := (sat_domRD κ').mp hκ'B
    obtain ⟨hd, hm, hdm⟩ := lineUpD_run l hl (ΨL s2) s2 hs2
      (by rw [hbase]; exact hκ'R.1)
      (by rw [hbase]; nlinarith [hωR.2])
    exact ⟨lineUpD (cAD l) (ΨL s2), lineUpD_zero (cAD l) (ΨL s2), hd, hm, hdm⟩

theorem seqB_of_AD (l : ℕ) : ∀ ν μ : State (Var 2),
    Program.sem (Program.ode (sysAD l) domRD) ν μ →
    Program.sem (Program.seq (Program.ode (sysBD l) domRD)
      (Program.ode (sysAD l) domRD)) ν μ := by
  intro ν μ hA
  have hdomν : Formula.sat domRD ν := by
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

theorem coupleAloneD (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt) (hv : VerdD l)
    (σ' : State (Var 2))
    (hσ' : Formula.sat (Formula.and (invLe gD) envD) σ') (htg0 : σ' tgD = 0)
    (hfar : σ' (Rv 0) ≤ 1 - cAD l * dt) :
    faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD l))) domLD)
      (Program.ode (rightBlock (fRD 1) (Term.const (lamD l))) domRD)
      (Formula.and (invLe gD) envD) tgD dt σ' := by
  have hupd : Function.update σ' tgD (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgD
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLD l) (fRD 1) (Term.const (lamD l))
    (Formula.and domLD domRD) [gD]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdD] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLD l) ++ rightBlock (fRD 1) (Term.const (lamD l)))
      (Formula.and domLD domRD)) (invLe gD)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gD
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gD σ').mp hσ'.1
  have hωR := (sat_domRD σ').mp hσ'.2.2
  have hES : HExistSegB (fLD l) (fRD 1) (Term.const (lamD l)) domLD domRD dt
      (Function.update σ' tgD 0) := by
    rw [hupd]
    exact esAloneD l hl dt hdt0 σ' hωR.1 hfar
  have hbase := segment_faModalB_from_certB gD (fLD l) (fRD 1) (Term.const (lamD l))
    domLD domRD tgD dt
    (LR_blocks_disjoint _ _ _ (hfLD l hl) (hfRD 1 (by norm_num)) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRD hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD l) _ h
      exact aux_ne_Lv aD i hi)
    (fun h => aux_notin_range_Lv aD (leftBlock_readVars_sub (fLD l) (hfLD l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRD 1) (Term.const (lamD l)) _ h
      exact aux_ne_Rv aD i hi)
    (fun h => aux_notin_range_Rv aD (rightBlock_readVars_sub (fRD 1)
      (Term.const (lamD l)) (hfRD 1 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aD (rightBlock_boundSet_sub (fRD 1)
      (Term.const (lamD l)) h))
    (fun h => aux_notin_range_Lv aD (hdomLD h))
    (fun h => aux_notin_range_Rv aD (hdomRD h))
    htggD hbox hES
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLD ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRD μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLD μ := by
    rwa [(Formula.coincidence domLD (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRD 1) (Term.const (lamD l)) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLD μ ↔ Formula.sat domLD ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem coupleD (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdD l) :
    ∀ σ', Formula.sat (Formula.and (invLe gD) envD) σ' → σ' tgD = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD l))) domLD)
        (Program.seq (Program.ode (rightBlock (fRD 2) (Term.const 1)) domRD)
          (Program.ode (rightBlock (fRD 1) (Term.const 1)) domRD))
        (Formula.and (invLe gD) envD) tgD dt σ' := by
  intro σ' hσ' htg0
  have hstretch : faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD l))) domLD)
      (Program.seq (Program.ode (sysBD l) domRD) (Program.ode (sysAD l) domRD))
      (Formula.and (invLe gD) envD) tgD dt σ' := by
    by_cases hc : 1 - cAD l * dt < σ' (Rv 0)
    · exact coupleSplitD l hl dt hdt0 hdt5 hv σ' hσ' hc
    · exact faModalB_monoQ (seqB_of_AD l)
        (coupleAloneD l hl dt hdt0 hv σ' hσ' htg0 (by linarith [not_lt.mp hc]))
  refine faModalB_monoQ ?_ hstretch
  intro ν μ hsem
  obtain ⟨κ, hB, hA⟩ := hsem
  exact ⟨κ, sem_rightBlock_reparam (lamD l) 1 (lamD_pos l) one_pos hB,
    sem_rightBlock_reparam (lamD l) 1 (lamD_pos l) one_pos hA⟩

/-! ## Assembly -/

noncomputable def pieceD : Program (Var 2) :=
  Program.seq (Program.ode (rightBlock (fRD 2) (Term.const 1)) domRD)
    (Program.ode (rightBlock (fRD 1) (Term.const 1)) domRD)

theorem coupleD' (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdD l) :
    ∀ σ, Formula.sat (Formula.and (invLe gD) envD) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD l))) domLD)
        pieceD (Formula.and (invLe gD) envD) tgD dt
        (Function.update σ tgD 0) := by
  intro σ hσ
  have htgφ : tgD ∉ (Formula.and (invLe gD) envD).fv := by
    intro h
    rcases h with h | h
    · exact htggD (by simpa [invLe, Formula.fv, Term.fv] using h)
    · exact htgenvD h
  have hupdφ : Formula.sat (Formula.and (invLe gD) envD)
      (Function.update σ tgD 0) := by
    rwa [(Formula.coincidence (Formula.and (invLe gD) envD) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (invLe gD) envD) _ ↔ _)]
  exact coupleD l hl dt hdt0 hdt5 hv (Function.update σ tgD 0) hupdφ
    (Function.update_self _ _ _)

theorem hdisPieceD (l : ℕ) (hl : l < 4) (dt : ℝ) :
    Disjoint (Program.vars (pieceD.rename (Equiv.refl (Var 2))))
      (Program.vars (clockedSeg (leftBlock (fLD l)) domLD tgD dt)) := by
  rw [Program.rename_refl, Set.disjoint_left]
  intro x hx hxW
  have hxR : x ∈ range Rv := by
    rcases vars_seq_sub _ _ hx with hx | hx <;>
      · rcases vars_ode_sub _ _ hx with hx | hx
        · rcases hx with hx | hx
          · exact rightBlock_boundSet_sub _ _ hx
          · refine rightBlock_readVars_sub _ (Term.const 1) ?_ (by simp [Term.fv]) hx
            first
              | exact hfRD 2 (by norm_num)
              | exact hfRD 1 (by norm_num)
        · exact hdomRD hx
  rcases vars_clockedSegL_sub (fLD l) domLD aD dt (hfLD l hl) hdomLD hxW with hx' | hx'
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

/-- The per-window response with a hop prefix of `hs` static hops. -/
theorem segD (l : ℕ) (hl : l < 4) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdD l) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (invLe gD) envD) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLD l)) domLD tgD dt (kD l))
      (bigSeq ((path.map (fun p =>
          Program.ode (rightBlock (fRD p) (Term.const 1)) domRD)) ++
        (List.replicate (kD l)
          [Program.ode (rightBlock (fRD 2) (Term.const 1)) domRD,
           Program.ode (rightBlock (fRD 1) (Term.const 1)) domRD]).flatten))
      (Formula.and (invLe gD) envD)) σ := by
  have hkpos : 0 < kD l := by
    interval_cases l <;> norm_num [kD]
  have hfa := Hmulti_windowR_prefixed (fLD l) domLD gD envD aD dt (kD l) htggD htgenvD
    (path.map (fun p => (⟨fRD p, Term.const 1, domRD⟩ : RepoHop 2)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRD p (hpath p hp), by simp [Term.fv], hdomRD⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fRD p)
        (lam := Term.const 1) (domR := domRD) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfLD l hl) hdomLD
    (List.replicate (kD l) pieceD) (by simp) hkpos
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hdisPieceD l hl dt)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleD' l hl dt hdt0 hdt5 hv σ' hσ')
    hσ
  rw [show (path.map (fun p => (⟨fRD p, Term.const 1, domRD⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = path.map (fun p => Program.ode (rightBlock (fRD p) (Term.const 1)) domRD)
    from by rw [List.map_map]; rfl] at hfa
  refine sat_faModal_monoR (fun ν μ hrun => ?_) hfa
  clear hfa
  induction path generalizing ν with
  | nil =>
      simpa using sem_seqPairs (kD l) _ _ ν μ (by simpa [pieceD] using hrun)
  | cons a as ih =>
      simp only [List.map_cons, List.cons_append, bigSeq] at hrun ⊢
      obtain ⟨κ, hhop, hrest⟩ := hrun
      exact ⟨κ, hhop, ih (fun p hp => hpath p (List.mem_cons_of_mem a hp)) κ hrest⟩

theorem HmultiD (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdD 0) (hv1 : VerdD 1) (hv2 : VerdD 2) (hv3 : VerdD 3) :
    ∀ P ∈ leftProgsD dt, ∀ (q : ℕ), q < GrD.modes.length → ∀ σ, σ mvD = (q : ℝ) →
      Formula.sat (Formula.and (invLe gD) envD) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gD) envD)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrD] using hq
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
  have hal : ∀ s ∈ [((0:ℕ), modeD 0, edgeD 0 1), ((1:ℕ), modeD 1, edgeD 1 2),
      ((2:ℕ), modeD 2, edgeD 2 1), ((1:ℕ), modeD 1, edgeD 1 1)],
      GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1 := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨GrD_modeAt 0 (by norm_num), edgeD_mem 0 1 (by simp [GrD])⟩
        | exact ⟨GrD_modeAt 1 (by norm_num), edgeD_mem 1 2 (by simp [GrD])⟩
        | exact ⟨GrD_modeAt 1 (by norm_num), edgeD_mem 1 1 (by simp [GrD])⟩
        | exact ⟨GrD_modeAt 2 (by norm_num), edgeD_mem 2 1 (by simp [GrD])⟩
  have halmem : ∀ s ∈ ([((2:ℕ), modeD 2, edgeD 2 1), ((1:ℕ), modeD 1, edgeD 1 2),
      ((2:ℕ), modeD 2, edgeD 2 1), ((1:ℕ), modeD 1, edgeD 1 1)] :
        List (ℕ × RMode (Var 2) × REdge (Var 2))),
      GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1 := by
    intro s hs
    refine hal s ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
    tauto
  simp only [leftProgsD, leftDataD, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hbody : ∀ (l : ℕ) (hl : l < 4) (hkv : VerdD l), ∀ (q' : ℕ), q' < 3 →
      σ mvD = (q' : ℝ) →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q') ∧
        Formula.sat (faModal (Equiv.refl (Var 2))
          (windowSeg (leftBlock (fLD l)) domLD tgD dt (kD l))
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gD) envD)) σ := by
    intro l hl hkv q' hq' hmv'
    have hk12 : kD l = 2 ∨ kD l = 1 := by
      interval_cases l <;> simp [kD]
    interval_cases q'
    · -- start Fast: hops [0, 1]
      rcases hk12 with hk | hk
      · refine ⟨(0, modeD 0, edgeD 0 1) :: (1, modeD 1, edgeD 1 2) ::
          [(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 2),
           (2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          (by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hal _ (by simp)
            · rcases List.mem_cons.mp hs with rfl | hs
              · exact hal _ (by simp)
              · exact halmem s hs),
          hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
            (hstep _ _ _ rfl (hsingle _))))),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [0, 1]
          (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeD, List.replicate, hk] using this
      · refine ⟨(0, modeD 0, edgeD 0 1) :: (1, modeD 1, edgeD 1 2) ::
          [(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          (by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hal _ (by simp)
            · rcases List.mem_cons.mp hs with rfl | hs
              · exact hal _ (by simp)
              · refine halmem s ?_
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
                tauto),
          hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [0, 1]
          (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeD, List.replicate, hk] using this
    · -- start Slow: hop [1]
      rcases hk12 with hk | hk
      · refine ⟨(1, modeD 1, edgeD 1 2) ::
          [(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 2),
           (2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          (by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hal _ (by simp)
            · exact halmem s hs),
          hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
            (hsingle _)))),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeD, List.replicate, hk] using this
      · refine ⟨(1, modeD 1, edgeD 1 2) ::
          [(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          (by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hal _ (by simp)
            · refine halmem s ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
              tauto),
          hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeD, List.replicate, hk] using this
    · -- start Return: no hop
      rcases hk12 with hk | hk
      · refine ⟨[(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 2),
           (2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          halmem,
          hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [] (by simp) hσ
        simpa [modeD, List.replicate, hk] using this
      · refine ⟨[(2, modeD 2, edgeD 2 1), (1, modeD 1, edgeD 1 1)],
          (by
            intro s hs
            refine halmem s ?_
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
            tauto),
          hstep _ _ _ rfl (hsingle _),
          (fun s hs => by rw [hhead1 _ _ _ hs]),
          ?_⟩
        have := segD l hl dt hdt0 hdt5 hkv [] (by simp) hσ
        simpa [modeD, List.replicate, hk] using this
  rcases hP with rfl | rfl | rfl | rfl
  · exact hbody 0 (by norm_num) hv0 q hq3 hmv
  · exact hbody 1 (by norm_num) hv1 q hq3 hmv
  · exact hbody 2 (by norm_num) hv2 q hq3 hmv
  · exact hbody 3 (by norm_num) hv3 q hq3 hmv

/-- **`arm_chain_rung2`, modal Theorem 3** — the asymmetric-rate switch, closing
the L3 class. -/
theorem arm_chain_rung2_modal (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdD 0) (hv1 : VerdD 1) (hv2 : VerdD 2) (hv3 : VerdD 3) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsD dt))
      (rightAutomatonBody GrD mvD)
      (RFormula.and (RFormula.and (canonInv gD) (envLR domLD domRD))
        (mvValidR mvD GrD.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrD mvD gD domLD domRD (leftProgsD dt)
    (canonInv gD) (encode_canonInv gD) ?_ ?_ ?_
  · exact hdis_multi GrD 0 1 dt leftDataD (by decide) httD hRvD hLD
  · exact hstep_assembled_multiE GrD mvD gD envD (leftProgsD dt) hmvgD hmvenvD
      hfreshD httD hltD (hframesD dt)
      (HmultiD dt hdt0 hdt5 hv0 hv1 hv2 hv3)
  · exact hddF_multiE GrD 0 1 dt leftDataD (canonInv gD) domLD domRD (by decide)
      httD hRvD hLD (canonInv_varsL gD hgD) (canonInv_varsR gD) hdomLD hdomRD

end ArmChainRung2Modal
end RelCertifier