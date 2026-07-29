/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_fidelity_low`, modal Theorem 3 (the L3 switch pilot)

The first intra-piece-switch instance. The PD arm (left, `θ' = v`,
`v' = −(θ − 0.5) − 2v`) refines a coarse two-mode constant-rate envelope (right,
`Approach θ' = +0.2`, `Return θ' = −0.2`) at tolerance `θ_L ≤ θ_R + 0.4`, coupled at
`λ = 5` with `k = 5` windows.

The landing mode is `Approach` for both windows, but an `Approach` response would
exit the right envelope (`θ_R ≤ 1`) mid-piece from near-ceiling anchors. Per piece
the response is the drop-tracked B-first split (L3′): from anchors with face room
(`θ_R ≤ 1 − dt`, at the λ-stretched rate `cA·λ = 1`) run `Approach` alone; from
near-ceiling anchors run `Return` for `θ = 1/2` of the piece and then `Approach` —
the rise exactly cancels the drop (`cA = cB = 0.2`), and the invariant charge
`MgB·θ·dt` is covered because near the ceiling the invariant has at least `0.4 −
dt` of slack. The dichotomy closes for `dt ≤ 1/5` — switch instances are dt-CAPPED,
unlike the dt-uniform instances landed so far.

Both split-branch phases and the A-alone branch discharge existence Z3-free (the
fields are constant-rate; explicit linear witnesses). The λ = 5 coupling converts
to the real λ = 1 automaton per piece via `sem_rightBlock_reparam` (L7's first
instantiation).

Residual: one route verdict pack (`VerdF` — the `Approach` coupling, per window).
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
import RelCertifier.Instances.BenchIR.arm_fidelity_low

namespace RelCertifier
namespace ArmFidelityLowModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsF : List String := ["theta", "v"]
def dummyF : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLF (l : ℕ) : Parse.PMode := arm_fidelity_low_IR.L.modes.getD l dummyF
def mRF (q : ℕ) : Parse.PMode := arm_fidelity_low_IR.R.modes.getD q dummyF

abbrev mvF : Var 2 := (Side.Aux, 0)
abbrev aF : Fin 2 := (1 : Fin 2)
abbrev tgF : Var 2 := (Side.Aux, aF)

noncomputable def fLF (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsF 2 Side.L (mLF l)
noncomputable def fRF (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsF 2 Side.R (mRF q)
noncomputable def domLF : Formula (Var 2) := hostEvolve vsF 2 Side.L (mLF 0)
noncomputable def domRF : Formula (Var 2) := hostEvolve vsF 2 Side.R (mRF 0)
noncomputable def envF : Formula (Var 2) := Formula.and domLF domRF

noncomputable def gF : Term (Var 2) :=
  ((Run.invToG vsF 2 ((arm_fidelity_low_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLF_pipe (l : ℕ) (i : Fin 2) : fLF l i =
    (((some (mLF l)).bind (Run.dynOf vsF 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRF_pipe (q : ℕ) (i : Fin 2) : fRF q i =
    (((some (mRF q)).bind (Run.dynOf vsF 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLF_pipe : domLF =
    (((some (mLF 0)).bind (fun m => Run.lowerF vsF 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRF_pipe : domRF =
    (((some (mRF 0)).bind (fun m => Run.lowerF vsF 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLF (l : ℕ) (hl : l < 2) : ∀ i, (fLF l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsF) (some (mLF l))
    (by interval_cases l <;>
      simp [mLF, arm_fidelity_low_IR, Parse.PExpr.namesFree]) i x (fLF_pipe l i ▸ hx))

theorem hfRF (q : ℕ) (hq : q < 2) : ∀ i, (fRF q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsF) (some (mRF q))
    (by interval_cases q <;>
      simp [mRF, arm_fidelity_low_IR, Parse.PExpr.namesFree]) i x (fRF_pipe q i ▸ hx))

theorem hdomLF : domLF.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsF) (some (mLF 0))
    (by simp [mLF, arm_fidelity_low_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLF_pipe ▸ hx))

theorem hdomRF : domRF.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsF) (some (mRF 0))
    (by simp [mRF, arm_fidelity_low_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRF_pipe ▸ hx))

theorem hgF : gF.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgF : mvF ∉ gF.fv := fun h => by
  rcases hgF h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggF : tgF ∉ gF.fv := fun h => by
  rcases hgF h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvF : mvF ∉ envF.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvF : tgF ∉ envF.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (the REAL λ = 1 automaton) -/

noncomputable def modeF (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRF q) (Term.const 1), dom := domRF, weight := 1 }

def edgeF (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrF : SearchGraph (Var 2) :=
  { modes := [modeF 0, modeF 1],
    edges := [edgeF 0 1, edgeF 0 0, edgeF 1 0, edgeF 1 1] }

theorem GrF_modeAt (q : ℕ) (hq : q < 2) : GrF.modeAt q = some (modeF q) := by
  interval_cases q <;> rfl

theorem httF : ∀ q, ∀ e ∈ GrF.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrF.edges := List.mem_of_mem_filter he
  simp only [GrF, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem hltF : ∀ q, ∀ e ∈ GrF.edgesFrom q, e.tgt < GrF.modes.length := by
  intro q e he
  have hmem : e ∈ GrF.edges := List.mem_of_mem_filter he
  simp only [GrF, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrF, edgeF]

theorem hRvF : ∀ q m, GrF.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeF q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrF] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrF] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrF])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRF q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRF q) (Term.const 1) (hfRF q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRF hy

theorem edgeF_mem : ∀ st tgt, edgeF st tgt ∈ GrF.edges →
    edgeF st tgt ∈ GrF.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeF]⟩

theorem hfreshF : ∀ q m, GrF.modeAt q = some m →
    mvF ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvF q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family (k = 5, plain windows) -/

noncomputable def leftDataF : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLF 0, domLF, 5), (fLF 1, domLF, 5)]

noncomputable def leftProgsF (dt : ℝ) : List (Program (Var 2)) :=
  leftDataF.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgF dt d.2.2)

theorem hLF : ∀ d ∈ leftDataF, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataF, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨hfLF 0 (by norm_num), hdomLF⟩
  · exact ⟨hfLF 1 (by norm_num), hdomLF⟩

theorem hframesF (dt : ℝ) : ∀ P ∈ leftProgsF dt, FramesMv P mvF := by
  intro P hP
  simp only [leftProgsF, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgF dt d.2.2 mvF (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm2 : Run.parseRat "-2" = some (-2) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm005 : Run.parseRat "-0.05" = some (-(1:ℚ)/20) := by
  have h : parseQ "-0.05" = some (⟨-5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field pins (right constant rates, per mode) -/

theorem fRF0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRF q 0) x = (if q = 0 then (1:ℝ)/5 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, arm_fidelity_low_IR, vsF, Run.dynOf, Run.lowerE,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRF1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRF q 1) x = 0 := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, arm_fidelity_low_IR, vsF, Run.dynOf, Run.lowerE,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

/-! ## The dom/invariant shapes -/

theorem sat_domRF (x : State (Var 2)) : Formula.sat domRF x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRF, hostEvolve, mRF, arm_fidelity_low_IR, vsF]
  simp [Run.lowerF, Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem gF_eval (x : State (Var 2)) :
    Term.eval gF x = x (Lv 0) - (x (Rv 0) + 2/5) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gF, arm_fidelity_low_IR, Run.invToG, Run.lowerE, vsF, hp04,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

theorem sat_domLF (x : State (Var 2)) : Formula.sat domLF x ↔
    (-(1:ℝ)/20 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1 ∧ -(1:ℝ) ≤ x (Lv 1) ∧ x (Lv 1) ≤ 1) := by
  simp only [domLF, hostEvolve, mLF, arm_fidelity_low_IR, vsF]
  simp [Run.lowerF, Run.lowerE, hpm005, hp10, hpm10, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Lv]
  tauto

/-- Left field, θ row: `θ' = v`. -/
theorem fLF0_eval (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    Term.eval (fLF l 0) x = x (Lv 1) := by
  interval_cases l <;>
    simp [fLF, hostDyn, mLF, arm_fidelity_low_IR, vsF, Run.dynOf, Run.lowerE,
      hp05, hpm1, hpm2, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Lv]

/-! ## The split systems (clocked left + λ-stretched right phases) -/

noncomputable def sysXF (l : ℕ) : ODESystem (Var 2) :=
  DLCalTiming.clk tgF (leftBlock (fLF l))
/-- Phase B: `Return` at λ = 5 (`θ_R' = −1`). -/
noncomputable def sysBF : ODESystem (Var 2) := rightBlock (fRF 1) (Term.const 5)
/-- Phase A: `Approach` at λ = 5 (`θ_R' = +1`). -/
noncomputable def sysAF : ODESystem (Var 2) := rightBlock (fRF 0) (Term.const 5)

theorem hwfXBF (l : ℕ) : (sysXF l ++ sysBF).WellFormed := by
  show (((sysXF l ++ sysBF).map Prod.fst)).Nodup
  simp only [sysXF, sysBF, DLCalTiming.clk, leftBlock, rightBlock, List.map_append,
    List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.finRange, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  decide

theorem hwfXAF (l : ℕ) : (sysXF l ++ sysAF).WellFormed := by
  show (((sysXF l ++ sysAF).map Prod.fst)).Nodup
  simp only [sysXF, sysAF, DLCalTiming.clk, leftBlock, rightBlock, List.map_append,
    List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.finRange, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  decide

/-- Two-coordinate affine Lie (mirror of `lie_affine_coord`). -/
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

/-! ## Field rows of the split systems -/

theorem memB_Rv0 : ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const 5) (fRF 1 0))
    ∈ sysBF := by
  simp only [sysBF, rightBlock, List.mem_map]
  exact ⟨0, List.mem_finRange 0, rfl⟩

theorem memX_Lv0 (l : ℕ) : ((Lv 0 : Var 2), fLF l 0) ∈ sysXF l := by
  simp only [sysXF, DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map]
  exact Or.inl ⟨0, List.mem_finRange 0, rfl⟩

theorem odeFieldXB_Rv0 (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    odeField (sysXF l ++ sysBF) x (Rv 0) = -1 := by
  have hmem : ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const 5) (fRF 1 0))
      ∈ sysXF l ++ sysBF := List.mem_append_right _ memB_Rv0
  have hb : (Rv 0 : Var 2) ∈ (sysXF l ++ sysBF).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXF l ++ sysBF) x (Rv 0)
      = ((sysXF l ++ sysBF).rhs (Rv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Rv 0 : Var 2) = ((Rv 0 : Var 2), Term.binop AOp.mul (Term.const 5)
      (fRF 1 0)).1 from rfl, ODESystem.rhs_eq_of_mem (hwfXBF l) hmem]
  simp [Term.eval, AOp.interp, fRF0_eval 1 (by norm_num)]

theorem odeFieldXB_Lv0 (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    odeField (sysXF l ++ sysBF) x (Lv 0) = x (Lv 1) := by
  have hmem : ((Lv 0 : Var 2), fLF l 0) ∈ sysXF l ++ sysBF :=
    List.mem_append_left _ (memX_Lv0 l)
  have hb : (Lv 0 : Var 2) ∈ (sysXF l ++ sysBF).bound := by
    simp only [ODESystem.bound, List.mem_map]
    exact ⟨_, hmem, rfl⟩
  rw [show odeField (sysXF l ++ sysBF) x (Lv 0)
      = ((sysXF l ++ sysBF).rhs (Lv 0)).eval x from by
    simp only [odeField, if_pos hb]]
  rw [show (Lv 0 : Var 2) = ((Lv 0 : Var 2), fLF l 0).1 from rfl,
    ODESystem.rhs_eq_of_mem (hwfXBF l) hmem]
  exact fLF0_eval l hl x

/-! ## The split-branch Lie facts -/

/-- The invariant charge in phase B: `dg/dt = v_L + 1 ≤ 2` on the envelope. -/
theorem hbndBF (l : ℕ) (hl : l < 2) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLF domRF) x →
    Lie (sysXF l ++ sysBF) (fun ν => Term.eval gF ν) x ≤ 2 := by
  intro x hx
  have hv : x (Lv 1) ≤ 1 := ((sat_domLF x).mp hx.1).2.2.2
  have hfun : (fun ν : State (Var 2) => Term.eval gF ν)
      = fun y => 1 * y (Lv 0) + (-1) * y (Rv 0) + (-(2/5)) := by
    funext y
    rw [gF_eval]
    ring
  rw [hfun, lie_affine_coord2 _ (hwfXBF l) (Lv 0) (Rv 0) 1 (-1) (-(2/5)) x,
    odeFieldXB_Lv0 l hl, odeFieldXB_Rv0 l hl]
  linarith

/-- The tracked-coordinate drop rate in phase B: `θ_R' = −1`. -/
theorem hjrowF (l : ℕ) (hl : l < 2) : ∀ x : State (Var 2),
    Formula.sat (Formula.and domLF domRF) x →
    Lie (sysXF l ++ sysBF) (fun ν => Term.eval (Term.var (Rv 0)) ν) x ≤ -1 := by
  intro x _
  have hfun : (fun ν : State (Var 2) => Term.eval (Term.var (Rv 0)) ν)
      = fun y => 1 * y (Rv 0) + 0 := by
    funext y
    simp [Term.eval]
  rw [hfun, lie_affine_coord _ (hwfXBF l) (Rv 0) 1 0 x, odeFieldXB_Rv0 l hl]
  norm_num

/-! ## Clock-anchored joint box (freeze `tg` along the clocked run) -/

/-- An unclocked joint box gives the clocked box at the SAME anchor: freeze `tg`
along the clocked run (the joint rows neither bind nor read it; the domain and
invariant are `tg`-free), yielding a joint run with the same non-`tg` endpoint. -/
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
          rcases hA with h | h
          · exact h
          · exact absurd (by simpa using h) hxtg
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

/-! ## The route-verdict residual and the certified `A` box -/

def VerdF (l : ℕ) : Prop :=
  z3solve (flowQuery ⟨gF, fLF l, fRF 0, Term.const 5,
    Formula.and domLF domRF⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gF, fLF l, fRF 0, Term.const 5,
    Formula.and domLF domRF⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gF, fLF l, fRF 0, Term.const 5,
    Formula.and domLF domRF⟩) = Verdict.unsat

theorem hboxAF (l : ℕ) (hl : l < 2) (hv : VerdF l) :
    ∀ κ : State (Var 2), Term.eval gF κ ≤ 0 →
      Formula.sat (Formula.box (Program.ode (sysXF l ++ sysAF)
        (Formula.and domLF domRF)) (Formula.and (invLe gF) envF)) κ := by
  intro κ hκ
  have hAll := segPresAll_from_strata_verdicts' (fLF l) (fRF 0) (Term.const 5)
    (Formula.and domLF domRF) [gF]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdF] using hv)
  have hjoint : Formula.sat (Formula.box (Program.ode
      (jointSys (fLF l) (fRF 0) (Term.const 5)) (Formula.and domLF domRF))
      (invLe gF)) κ := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll κ ?_ ω hω gF List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hκ
  have htgLb : tgF ∉ (leftBlock (fLF l)).bound := by
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ h
    exact aux_ne_Lv aF i hi
  have htgAb' : tgF ∉ (rightBlock (fRF 0) (Term.const 5)).bound := by
    intro h
    obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRF 0) (Term.const 5) _ h
    exact aux_ne_Rv aF i hi
  have htgLr : tgF ∉ (leftBlock (fLF l)).readVars := fun h =>
    aux_notin_range_Lv aF (leftBlock_readVars_sub (fLF l) (hfLF l hl) h)
  have htgAr' : tgF ∉ (rightBlock (fRF 0) (Term.const 5)).readVars := fun h =>
    aux_notin_range_Rv aF (rightBlock_readVars_sub (fRF 0) (Term.const 5)
      (hfRF 0 (by norm_num)) (by simp [Term.fv]) h)
  have htgdom : tgF ∉ (Formula.and domLF domRF).fv := by
    simp only [Formula.fv, Set.mem_union, not_or]
    exact ⟨fun h => aux_notin_range_Lv aF (hdomLF h),
      fun h => aux_notin_range_Rv aF (hdomRF h)⟩
  have hclk := box_clk_anchor gF (leftBlock (fLF l))
    (rightBlock (fRF 0) (Term.const 5)) (Formula.and domLF domRF) tgF
    htgLb htgAb' htgLr htgAr' htgdom htggF
    (by rw [← jointSys_split]; exact hjoint)
  rw [sat_box] at hclk ⊢
  intro ω hω
  refine ⟨hclk ω hω, sem_ode_ends_in_domain hω⟩

/-! ## Linear existence witnesses (constant-rate right fields, Z3-free) -/

/-- The rising right line (`Approach` at λ = 5: `θ_R' = +1`). -/
noncomputable def lineUp (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) + t)

/-- The falling right line (`Return` at λ = 5: `θ_R' = −1`). -/
noncomputable def lineDn (base : State (Var 2)) (t : ℝ) : State (Var 2) :=
  Function.update base (Rv 0) (base (Rv 0) - t)

theorem lineUp_zero (base : State (Var 2)) : lineUp base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineUp, Function.update_self]
  · simp [lineUp, Function.update_of_ne hx]

theorem lineDn_zero (base : State (Var 2)) : lineDn base 0 = base := by
  funext x
  by_cases hx : x = (Rv 0 : Var 2)
  · subst hx; simp [lineDn, Function.update_self]
  · simp [lineDn, Function.update_of_ne hx]

/-- Derivative/mask/domain bundle for a rising `Approach` (λ = 5) segment. -/
theorem lineUp_run (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : 0 ≤ base (Rv 0)) (hhi : base (Rv 0) + s ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRF 0) (Term.const 5),
      HasDerivWithinAt (fun u => lineUp base u p.1) (p.2.eval (lineUp base t))
        (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRF 0) (Term.const 5)).bound →
      lineUp base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRF (lineUp base t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineUp base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 0 0)) (lineUp base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 0 0))
          (lineUp base t) = 1 := by
        simp [Term.eval, AOp.interp, fRF0_eval 0 (by norm_num)]
      rw [heval]
      have hfun : (fun u => lineUp base u (Rv 0)) = fun u => base (Rv 0) + u := by
        funext u
        simp [lineUp, Function.update_self]
      rw [hfun]
      simpa using ((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_add (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineUp base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 0 1)) (lineUp base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 0 1))
          (lineUp base t) = 0 := by
        simp [Term.eval, AOp.interp, fRF1_eval 0 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineUp base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineUp, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineUp, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRF]
    constructor
    · simp only [lineUp, Function.update_self]
      linarith [ht.1]
    · simp only [lineUp, Function.update_self]
      linarith [ht.2]

/-- Derivative/mask/domain bundle for a falling `Return` (λ = 5) segment. -/
theorem lineDn_run (base : State (Var 2)) (s : ℝ) (hs : 0 ≤ s)
    (hlo : s ≤ base (Rv 0)) (hhi : base (Rv 0) ≤ 1) :
    (∀ t ∈ Icc (0:ℝ) s, ∀ p ∈ rightBlock (fRF 1) (Term.const 5),
      HasDerivWithinAt (fun u => lineDn base u p.1) (p.2.eval (lineDn base t))
        (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0:ℝ) s, ∀ x, x ∉ (rightBlock (fRF 1) (Term.const 5)).bound →
      lineDn base t x = base x) ∧
    (∀ t ∈ Icc (0:ℝ) s, Formula.sat domRF (lineDn base t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    fin_cases j
    · show HasDerivWithinAt (fun u => lineDn base u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 1 0)) (lineDn base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 1 0))
          (lineDn base t) = -1 := by
        simp [Term.eval, AOp.interp, fRF0_eval 1 (by norm_num)]
      rw [heval]
      have hfun : (fun u => lineDn base u (Rv 0)) = fun u => base (Rv 0) - u := by
        funext u
        simp [lineDn, Function.update_self]
      rw [hfun]
      simpa using ((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_sub (base (Rv 0)))
    · show HasDerivWithinAt (fun u => lineDn base u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 1 1)) (lineDn base t))
        (Icc 0 s) t
      have heval : Term.eval (Term.binop AOp.mul (Term.const 5) (fRF 1 1))
          (lineDn base t) = 0 := by
        simp [Term.eval, AOp.interp, fRF1_eval 1 (by norm_num)]
      rw [heval]
      have hne : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hfun : (fun u => lineDn base u (Rv 1)) = fun _ => base (Rv 1) := by
        funext u
        simp [lineDn, Function.update_of_ne hne]
      rw [hfun]
      exact hasDerivWithinAt_const t _ (base (Rv 1))
  · intro t ht x hx
    have hne : x ≠ (Rv 0 : Var 2) := by
      intro hc
      subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [lineDn, Function.update_of_ne hne]
  · intro t ht
    rw [sat_domRF]
    constructor
    · simp only [lineDn, Function.update_self]
      linarith [ht.2]
    · simp only [lineDn, Function.update_self]
      linarith [ht.1]

/-- **A-alone existence** from far anchors (`θ_R ≤ 1 − dt`): the rising line has
room for the whole window. -/
theorem esAloneF (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (ω : State (Var 2)) (hω0 : 0 ≤ ω (Rv 0)) (hωfar : ω (Rv 0) ≤ 1 - dt) :
    HExistSegB (fLF l) (fRF 0) (Term.const 5) domLF domRF dt ω := by
  intro s ΦL hs0 hsdt hΦL0 hder hmask hdom
  have hbase : ΦL s (Rv 0) = ω (Rv 0) := by
    refine hmask s (right_mem_Icc.mpr hs0) (Rv 0) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  obtain ⟨hd, hm, hdm⟩ := lineUp_run (ΦL s) s hs0
    (by rw [hbase]; exact hω0)
    (by rw [hbase]; linarith)
  exact ⟨lineUp (ΦL s), lineUp_zero (ΦL s), hd, hm, hdm⟩

end ArmFidelityLowModal
end RelCertifier
