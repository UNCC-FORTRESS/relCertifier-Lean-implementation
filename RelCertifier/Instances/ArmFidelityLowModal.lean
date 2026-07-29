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

/-! ## Shared side conditions for the split lemma -/

theorem htgX (l : ℕ) : (tgF, Term.const 1) ∈ sysXF l := by
  show (tgF, Term.const 1) ∈ leftBlock (fLF l) ++ [(tgF, Term.const 1)]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem hRv0notX (l : ℕ) : (Rv 0 : Var 2) ∉ (sysXF l).bound := by
  intro h
  simp only [sysXF, DLCalTiming.clk, ODESystem.bound, List.map_append,
    List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ h
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [tgF, Rv, Prod.ext_iff])

theorem hdisjXR (l : ℕ) (hl : l < 2) (q : ℕ) (hq : q < 2) :
    Disjoint ((sysXF l).boundSet ∪ (sysXF l).readVars)
      ((rightBlock (fRF q) (Term.const 5)).boundSet
        ∪ (rightBlock (fRF q) (Term.const 5)).readVars) := by
  rw [Set.disjoint_left]
  intro x hxX hxR
  have hxRv : x ∈ range Rv := by
    rcases hxR with h | h
    · exact rightBlock_boundSet_sub (fRF q) (Term.const 5) h
    · exact rightBlock_readVars_sub (fRF q) (Term.const 5) (hfRF q hq)
        (by simp [Term.fv]) h
  obtain ⟨i, hi⟩ := hxRv
  rcases hxX with h | h
  · rw [sysXF, clk_boundSet] at h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub (fLF l) h
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hi
      exact absurd hi (by simp [tgF, Rv, Prod.ext_iff])
  · rw [sysXF, clk_readVars] at h
    have := leftBlock_readVars_sub (fLF l) (hfLF l hl) h
    obtain ⟨j, hj⟩ := this
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

/-! ## The split branch (near-ceiling anchors) -/

theorem coupleSplitF (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt)
    (hdt5 : dt ≤ 1/5) (hv : VerdF l) (ω : State (Var 2))
    (hσ : Formula.sat (Formula.and (invLe gF) envF) ω)
    (hnear : 1 - dt < ω (Rv 0)) :
    faModalB (Equiv.refl (Var 2)) (Program.ode (sysXF l) domLF)
      (Program.seq (Program.ode sysBF domRF) (Program.ode sysAF domRF))
      (Formula.and (invLe gF) envF) tgF dt ω := by
  have hωL := (sat_domLF ω).mp hσ.2.1
  have hωR := (sat_domRF ω).mp hσ.2.2
  refine faModal_ODE_split_bounded (sysXF l) sysBF sysAF
    domLF domRF domRF (Formula.and (invLe gF) envF)
    gF 2 (by norm_num) (Rv 0) 1 (1/2) dt (by norm_num) (by norm_num)
    tgF (htgX l) (hwfXBF l) (hdisjXR l hl 1 (by norm_num)) (hdisjXR l hl 0 (by norm_num))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ω (hbndBF l hl) (hjrowF l hl) ?_ ?_ ?_ ?_
  · -- hφx
    intro x hx
    obtain ⟨i, hi⟩ := hdomLF hx
    subst hi
    exact Or.inl (by rw [sysXF, clk_boundSet]; exact Or.inl (Lv_mem_leftBlock_boundSet _ i))
  · -- hφyB
    intro x hx
    obtain ⟨i, hi⟩ := hdomRF hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · -- hφyA
    intro x hx
    obtain ⟨i, hi⟩ := hdomRF hx
    subst hi
    exact Or.inl (Rv_mem_rightBlock_boundSet _ _ i)
  · -- hXreads
    intro x hx
    rw [sysXF, clk_readVars] at hx
    obtain ⟨i, hi⟩ := leftBlock_readVars_sub (fLF l) (hfLF l hl) hx
    subst hi
    rw [sysXF, clk_boundSet]
    exact Or.inl (Lv_mem_leftBlock_boundSet _ i)
  · -- hBreads
    intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRF 1) (Term.const 5)
      (hfRF 1 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · -- hAreads
    intro x hx
    obtain ⟨i, hi⟩ := rightBlock_readVars_sub (fRF 0) (Term.const 5)
      (hfRF 0 (by norm_num)) (by simp [Term.fv]) hx
    subst hi
    exact Rv_mem_rightBlock_boundSet _ _ i
  · -- hABb
    intro x
    simp [sysAF, sysBF, rightBlock, ODESystem.bound, List.map_map, Function.comp_def]
  · -- hg0: near the ceiling the invariant has ≥ 0.4 − dt of slack
    have hg := gF_eval ω
    rw [hg]
    linarith [hωL.2.1]
  · -- hboxA
    intro κ hκ
    exact hboxAF l hl hv κ hκ
  · -- hExistB: the falling Return line from the near-ceiling anchor
    intro s1 ΦL hs10 hs1dt hΦL0 hder hmask hdoms
    have hbase : ΦL s1 (Rv 0) = ω (Rv 0) :=
      hmask s1 (right_mem_Icc.mpr hs10) (Rv 0) (hRv0notX l)
    obtain ⟨hd, hm, hdm⟩ := lineDn_run (ΦL s1) s1 hs10
      (by rw [hbase]; nlinarith)
      (by rw [hbase]; exact hωR.2)
    exact ⟨lineDn (ΦL s1), lineDn_zero (ΦL s1), hd, hm, hdm⟩
  · -- hExistA: the rising Approach line from the dropped switch state
    intro s1 s2 ΨL κ' hs1 hs2 hs2dt hfr hdrop hΨ0 hΨder hΨmask hΨdom hκ'B hκ'g
    have hs1s2 : s1 = s2 := by linarith
    have hbase : ΨL s2 (Rv 0) = κ' (Rv 0) :=
      hΨmask s2 (right_mem_Icc.mpr hs2) (Rv 0) (hRv0notX l)
    have hκ'R := (sat_domRF κ').mp hκ'B
    obtain ⟨hd, hm, hdm⟩ := lineUp_run (ΨL s2) s2 hs2
      (by rw [hbase]; exact hκ'R.1)
      (by rw [hbase]; nlinarith [hωR.2])
    exact ⟨lineUp (ΨL s2), lineUp_zero (ΨL s2), hd, hm, hdm⟩

/-! ## The A-alone branch (far anchors), embedded into the seq shape -/

/-- An `Approach`-only response is a `Return;Approach` response with a
zero-duration `Return` stretch. -/
theorem seqB_of_A : ∀ ν μ : State (Var 2),
    Program.sem (Program.ode sysAF domRF) ν μ →
    Program.sem (Program.seq (Program.ode sysBF domRF) (Program.ode sysAF domRF)) ν μ := by
  intro ν μ hA
  have hdomν : Formula.sat domRF ν := by
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

theorem coupleAloneF (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt) (hv : VerdF l)
    (σ' : State (Var 2))
    (hσ' : Formula.sat (Formula.and (invLe gF) envF) σ') (htg0 : σ' tgF = 0)
    (hfar : σ' (Rv 0) ≤ 1 - dt) :
    faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF l))) domLF)
      (Program.ode (rightBlock (fRF 0) (Term.const 5)) domRF)
      (Formula.and (invLe gF) envF) tgF dt σ' := by
  have hupd : Function.update σ' tgF (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgF
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLF l) (fRF 0) (Term.const 5)
    (Formula.and domLF domRF) [gF]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdF] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLF l) ++ rightBlock (fRF 0) (Term.const 5))
      (Formula.and domLF domRF)) (invLe gF)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gF
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gF σ').mp hσ'.1
  have hωR := (sat_domRF σ').mp hσ'.2.2
  have hES : HExistSegB (fLF l) (fRF 0) (Term.const 5) domLF domRF dt
      (Function.update σ' tgF 0) := by
    rw [hupd]
    exact esAloneF l hl dt hdt0 σ' hωR.1 hfar
  have hbase := segment_faModalB_from_certB gF (fLF l) (fRF 0) (Term.const 5)
    domLF domRF tgF dt
    (LR_blocks_disjoint _ _ _ (hfLF l hl) (hfRF 0 (by norm_num)) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLF hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRF hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ h
      exact aux_ne_Lv aF i hi)
    (fun h => aux_notin_range_Lv aF (leftBlock_readVars_sub (fLF l) (hfLF l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRF 0) (Term.const 5) _ h
      exact aux_ne_Rv aF i hi)
    (fun h => aux_notin_range_Rv aF (rightBlock_readVars_sub (fRF 0) (Term.const 5)
      (hfRF 0 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aF (rightBlock_boundSet_sub (fRF 0) (Term.const 5) h))
    (fun h => aux_notin_range_Lv aF (hdomLF h))
    (fun h => aux_notin_range_Rv aF (hdomRF h))
    htggF hbox hES
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLF ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRF μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLF μ := by
    rwa [(Formula.coincidence domLF (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLF hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRF 0) (Term.const 5) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLF μ ↔ Formula.sat domLF ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## The uniform per-piece coupling (dichotomy + λ-reparam) -/

/-- **The switch-piece coupling**: every anchor is served by the `Return;Approach`
response — far anchors ride `Approach` alone (a zero-duration `Return` stretch),
near-ceiling anchors take the drop-tracked B-first split. The λ = 5 phases convert
to the REAL λ = 1 mode programs per component (L7). -/
theorem coupleF (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdF l) :
    ∀ σ', Formula.sat (Formula.and (invLe gF) envF) σ' → σ' tgF = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF l))) domLF)
        (Program.seq (Program.ode (rightBlock (fRF 1) (Term.const 1)) domRF)
          (Program.ode (rightBlock (fRF 0) (Term.const 1)) domRF))
        (Formula.and (invLe gF) envF) tgF dt σ' := by
  intro σ' hσ' htg0
  have hstretch : faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF l))) domLF)
      (Program.seq (Program.ode sysBF domRF) (Program.ode sysAF domRF))
      (Formula.and (invLe gF) envF) tgF dt σ' := by
    by_cases hc : 1 - dt < σ' (Rv 0)
    · exact coupleSplitF l hl dt hdt0 hdt5 hv σ' hσ' hc
    · exact faModalB_monoQ seqB_of_A
        (coupleAloneF l hl dt hdt0 hv σ' hσ' htg0 (by linarith [not_lt.mp hc]))
  refine faModalB_monoQ ?_ hstretch
  intro ν μ hsem
  obtain ⟨κ, hB, hA⟩ := hsem
  exact ⟨κ, sem_rightBlock_reparam 5 1 (by norm_num) one_pos hB,
    sem_rightBlock_reparam 5 1 (by norm_num) one_pos hA⟩

/-! ## Assembly (k = 5 windows over the switch piece) -/

/-- The switch piece at the real λ = 1: `Return ; Approach`. -/
noncomputable def pieceF : Program (Var 2) :=
  Program.seq (Program.ode (rightBlock (fRF 1) (Term.const 1)) domRF)
    (Program.ode (rightBlock (fRF 0) (Term.const 1)) domRF)

/-- Update-anchored transport of the dichotomy coupling (the windowR shape). -/
theorem coupleF' (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdF l) :
    ∀ σ, Formula.sat (Formula.and (invLe gF) envF) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF l))) domLF)
        pieceF (Formula.and (invLe gF) envF) tgF dt
        (Function.update σ tgF 0) := by
  intro σ hσ
  have htgφ : tgF ∉ (Formula.and (invLe gF) envF).fv := by
    intro h
    rcases h with h | h
    · exact htggF (by simpa [invLe, Formula.fv, Term.fv] using h)
    · exact htgenvF h
  have hupdφ : Formula.sat (Formula.and (invLe gF) envF)
      (Function.update σ tgF 0) := by
    rwa [(Formula.coincidence (Formula.and (invLe gF) envF) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (invLe gF) envF) _ ↔ _)]
  exact coupleF l hl dt hdt0 hdt5 hv (Function.update σ tgF 0) hupdφ
    (Function.update_self _ _ _)

/-- The switch piece is right-side (its disjointness against the left window). -/
theorem hdisPieceF (l : ℕ) (hl : l < 2) (dt : ℝ) :
    Disjoint (Program.vars (pieceF.rename (Equiv.refl (Var 2))))
      (Program.vars (clockedSeg (leftBlock (fLF l)) domLF tgF dt)) := by
  rw [Program.rename_refl, Set.disjoint_left]
  intro x hx hxW
  have hxR : x ∈ range Rv := by
    rcases vars_seq_sub _ _ hx with hx | hx <;>
      · rcases vars_ode_sub _ _ hx with hx | hx
        · rcases hx with hx | hx
          · exact rightBlock_boundSet_sub _ _ hx
          · refine rightBlock_readVars_sub _ (Term.const 1) ?_ (by simp [Term.fv]) hx
            first
              | exact hfRF 1 (by norm_num)
              | exact hfRF 0 (by norm_num)
        · exact hdomRF hx
  rcases vars_clockedSegL_sub (fLF l) domLF aF dt (hfLF l hl) hdomLF hxW with hx' | hx'
  · rw [Set.mem_singleton_iff] at hx'
    obtain ⟨i, hi⟩ := hxR
    rw [hx'] at hi
    exact absurd hi (by simp [Rv, Prod.ext_iff])
  · obtain ⟨i, hi⟩ := hxR
    obtain ⟨j, hj⟩ := hx'
    rw [← hi] at hj
    exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- Runs of `k` replicated `seq p q` pieces are runs of the interleaved `[p, q, …]`. -/
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

/-- The per-window response (start `Return`): five switch pieces. -/
theorem segRet (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdF l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (invLe gF) envF) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLF l)) domLF tgF dt 5)
      (bigSeq ((List.replicate 5 [Program.ode (rightBlock (fRF 1) (Term.const 1)) domRF,
        Program.ode (rightBlock (fRF 0) (Term.const 1)) domRF]).flatten))
      (Formula.and (invLe gF) envF)) σ := by
  have hfa := Hmulti_windowR_prefixed (fLF l) domLF gF envF aF dt 5 htggF htgenvF
    [] (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfLF l hl) hdomLF
    (List.replicate 5 pieceF) (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hdisPieceF l hl dt)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleF' l hl dt hdt0 hdt5 hv σ' hσ')
    hσ
  simp only [List.map_nil, List.nil_append] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_seqPairs 5 _ _ ν μ hrun) hfa

/-- The per-window response (start `Approach`): a static hop to `Return`, then five
switch pieces. -/
theorem segApp (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv : VerdF l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (invLe gF) envF) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLF l)) domLF tgF dt 5)
      (bigSeq (Program.ode (rightBlock (fRF 0) (Term.const 1)) domRF ::
        (List.replicate 5 [Program.ode (rightBlock (fRF 1) (Term.const 1)) domRF,
          Program.ode (rightBlock (fRF 0) (Term.const 1)) domRF]).flatten))
      (Formula.and (invLe gF) envF)) σ := by
  have hfa := Hmulti_windowR_prefixed (fLF l) domLF gF envF aF dt 5 htggF htgenvF
    [⟨fRF 0, Term.const 1, domRF⟩]
    (by
      intro h hh
      rw [List.mem_singleton] at hh
      subst hh
      exact ⟨hfRF 0 (by norm_num), by simp [Term.fv], hdomRF⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' htg'
      rw [List.mem_singleton] at hh
      subst hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fRF 0)
        (lam := Term.const 1) (domR := domRF) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfLF l hl) hdomLF
    (List.replicate 5 pieceF) (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hdisPieceF l hl dt)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleF' l hl dt hdt0 hdt5 hv σ' hσ')
    hσ
  refine sat_faModal_monoR (fun ν μ hrun => ?_) hfa
  simp only [List.map_cons, List.map_nil, List.singleton_append, bigSeq] at hrun ⊢
  obtain ⟨κ, hhop, hrest⟩ := hrun
  exact ⟨κ, hhop, sem_seqPairs 5 _ _ κ μ hrest⟩

/-! ## The step provider and the final theorem -/

theorem HmultiF (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdF 0) (hv1 : VerdF 1) :
    ∀ P ∈ leftProgsF dt, ∀ (q : ℕ), q < GrF.modes.length → ∀ σ, σ mvF = (q : ℝ) →
      Formula.sat (Formula.and (invLe gF) envF) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrF.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrF.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gF) envF)) σ := by
  intro P hP q hq σ hmv hσ
  have hq2 : q < 2 := by simpa [GrF] using hq
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
  have halign : ∀ st tgt, edgeF st tgt ∈ GrF.edges → st < 2 →
      ∀ s ∈ ([] : List ℕ), True := fun _ _ _ _ _ _ => trivial
  simp only [leftProgsF, leftDataF, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  -- the ten-seg switch tail (Return-start) and its hop-prefixed variant
  have pairsegs : List (ℕ × RMode (Var 2) × REdge (Var 2)) :=
    [(1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
     (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
     (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
     (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
     (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 0)]
  rcases hP with rfl | rfl
  all_goals interval_cases q
  -- window Accelerate, start Approach
  · refine ⟨(0, modeF 0, edgeF 0 1) ::
      [(1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 1 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 0 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 1 (by norm_num), edgeF_mem 1 0 (by simp [GrF])⟩
    · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))))))))))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := segApp 0 (by norm_num) dt hdt0 hdt5 hv0 hσ
      simpa [modeF, List.replicate] using this
  -- window Accelerate, start Return
  · refine ⟨[(1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 1 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 0 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 1 (by norm_num), edgeF_mem 1 0 (by simp [GrF])⟩
    · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hsingle _)))))))))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := segRet 0 (by norm_num) dt hdt0 hdt5 hv0 hσ
      simpa [modeF, List.replicate] using this
  -- window Brake, start Approach
  · refine ⟨(0, modeF 0, edgeF 0 1) ::
      [(1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 1 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 0 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 1 (by norm_num), edgeF_mem 1 0 (by simp [GrF])⟩
    · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))))))))))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := segApp 1 (by norm_num) dt hdt0 hdt5 hv1 hσ
      simpa [modeF, List.replicate] using this
  -- window Brake, start Return
  · refine ⟨[(1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 1),
       (1, modeF 1, edgeF 1 0), (0, modeF 0, edgeF 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 1 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 0 (by norm_num), edgeF_mem 0 0 (by simp [GrF])⟩
          | exact ⟨GrF_modeAt 1 (by norm_num), edgeF_mem 1 0 (by simp [GrF])⟩
    · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hstep _ _ _ rfl (hsingle _)))))))))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := segRet 1 (by norm_num) dt hdt0 hdt5 hv1 hσ
      simpa [modeF, List.replicate] using this

/-- **`arm_fidelity_low`, modal Theorem 3 — the L3 switch pilot.** dt-capped at the
tool's window duration; the intra-piece switch (`Return;Approach` with the
drop-tracked split) serves every anchor. Residuals: the two window route verdicts. -/
theorem arm_fidelity_low_modal (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5)
    (hv0 : VerdF 0) (hv1 : VerdF 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInv gF) (envLR domLF domRF))
        (mvValidR mvF GrF.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrF mvF gF domLF domRF (leftProgsF dt)
    (canonInv gF) (encode_canonInv gF) ?_ ?_ ?_
  · exact hdis_multi GrF 0 1 dt leftDataF (by decide) httF hRvF hLF
  · exact hstep_assembled_multiE GrF mvF gF envF (leftProgsF dt) hmvgF hmvenvF
      hfreshF httF hltF (hframesF dt)
      (HmultiF dt hdt0 hdt5 hv0 hv1)
  · exact hddF_multiE GrF 0 1 dt leftDataF (canonInv gF) domLF domRF (by decide)
      httF hRvF hLF (canonInv_varsL gF hgF) (canonInv_varsR gF) hdomLF hdomRF

end ArmFidelityLowModal
end RelCertifier
