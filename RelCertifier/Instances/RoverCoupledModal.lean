/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `rover_coupled`, modal Theorem 3 (multiF, GENERATED)

The CATCH-UP form at n = 4 (skeleton generated, tail hand-written from the
`Rover3M1Modal` template): responses ride `faModal`'s post-window semantics —
zero-duration hops to Safe plus one hold run of `8·dt`, with the invariant
re-established by endpoint arithmetic (velocity floor `v_x ≥ 1/4`). The
`py`/`vy` coordinates are spectators.

Residuals: NONE. Z3-free — axioms are exactly the standard three.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.rover_coupled

namespace RelCertifier
namespace RoverCoupledModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 12800000

def vsC2 : List String := ["px", "py", "vx", "vy"]
def dummyC2 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLC2 (l : ℕ) : Parse.PMode := rover_coupled_IR.L.modes.getD l dummyC2
def mRC2 (q : ℕ) : Parse.PMode := rover_coupled_IR.R.modes.getD q dummyC2

abbrev mvC2 : Var 4 := (Side.Aux, 0)
abbrev aC2 : Fin 4 := (1 : Fin 4)
abbrev tgC2 : Var 4 := (Side.Aux, aC2)

noncomputable def fLC2 (l : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsC2 4 Side.L (mLC2 l)
noncomputable def fRC2 (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsC2 4 Side.R (mRC2 q)
noncomputable def domLC2 : Formula (Var 4) := hostEvolve vsC2 4 Side.L (mLC2 0)
noncomputable def domRC2 : Formula (Var 4) := hostEvolve vsC2 4 Side.R (mRC2 0)
noncomputable def envC2 : Formula (Var 4) := Formula.and domLC2 domRC2

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invC2PF : Parse.PForm :=
  (rover_coupled_IR.invariants.getD 2 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 4) :=
  ((Run.invToG vsC2 4 ((atomsOf invC2PF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gC2 : Term (Var 4) := gAt 0
noncomputable def gsC2 : List (Term (Var 4)) := []

/-! ## Side-splits -/

theorem fLC2_pipe (l : ℕ) (i : Fin 4) : fLC2 l i =
    (((some (mLC2 l)).bind (Run.dynOf vsC2 4 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRC2_pipe (q : ℕ) (i : Fin 4) : fRC2 q i =
    (((some (mRC2 q)).bind (Run.dynOf vsC2 4 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLC2_pipe : domLC2 =
    (((some (mLC2 0)).bind (fun m => Run.lowerF vsC2 4 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRC2_pipe : domRC2 =
    (((some (mRC2 0)).bind (fun m => Run.lowerF vsC2 4 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLC2 (l : ℕ) (hl : l < 3) : ∀ i, (fLC2 l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsC2) (some (mLC2 l))
    (by interval_cases l <;>
      simp [mLC2, rover_coupled_IR, Parse.PExpr.namesFree]) i x
    (fLC2_pipe l i ▸ hx))

theorem hfRC2 (q : ℕ) (hq : q < 3) : ∀ i, (fRC2 q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsC2) (some (mRC2 q))
    (by interval_cases q <;>
      simp [mRC2, rover_coupled_IR, Parse.PExpr.namesFree]) i x
    (fRC2_pipe q i ▸ hx))

theorem hdomLC2 : domLC2.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsC2) (some (mLC2 0))
    (by simp [mLC2, rover_coupled_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLC2_pipe ▸ hx))

theorem hdomRC2 : domRC2.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsC2) (some (mRC2 0))
    (by simp [mRC2, rover_coupled_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRC2_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gC2 :: gsC2, mvC2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gC2, gsC2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gC2 :: gsC2, tgC2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gC2, gsC2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFC2 : mvC2 ∉ (FM gC2 gsC2).fv := notMem_FM_fv hmvg
theorem htgFC2 : tgC2 ∉ (FM gC2 gsC2).fv := notMem_FM_fv htgg

theorem hmvenvC2 : mvC2 ∉ envC2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvC2 : tgC2 ∉ envC2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (one-way chain) -/

noncomputable def modeC2 (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRC2 q) (Term.const 1), dom := domRC2, weight := 1 }

def edgeC2 (st tgt : ℕ) : REdge (Var 4) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrC2 : SearchGraph (Var 4) :=
  { modes := [modeC2 0, modeC2 1, modeC2 2],
    edges := [edgeC2 0 1, edgeC2 0 0, edgeC2 1 2, edgeC2 1 1, edgeC2 2 2] }

theorem GrC2_modeAt (q : ℕ) (hq : q < 3) : GrC2.modeAt q = some (modeC2 q) := by
  interval_cases q <;> rfl

theorem httC2 : ∀ q, ∀ e ∈ GrC2.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrC2.edges := List.mem_of_mem_filter he
  simp only [GrC2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltC2 : ∀ q, ∀ e ∈ GrC2.edgesFrom q, e.tgt < GrC2.modes.length := by
  intro q e he
  have hmem : e ∈ GrC2.edges := List.mem_of_mem_filter he
  simp only [GrC2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrC2, edgeC2]

theorem hRvC2 : ∀ q m, GrC2.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeC2 q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC2] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC2] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC2] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrC2])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRC2 q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRC2 q) (Term.const 1) (hfRC2 q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRC2 hy

theorem edgeC2_mem : ∀ st tgt, edgeC2 st tgt ∈ GrC2.edges →
    edgeC2 st tgt ∈ GrC2.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeC2]⟩

theorem hfreshC2 : ∀ q m, GrC2.modeAt q = some m →
    mvC2 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvC2 q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataC2 : List ((Fin 4 → Term (Var 4)) × Formula (Var 4) × ℕ) :=
  [(fLC2 0, domLC2, 2), (fLC2 1, domLC2, 2), (fLC2 2, domLC2, 2)]

noncomputable def leftProgsC2 (dt : ℝ) : List (Program (Var 4)) :=
  leftDataC2.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgC2 dt d.2.2)

theorem hLC2 : ∀ d ∈ leftDataC2, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataC2, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLC2 0 (by norm_num), hdomLC2⟩
  · exact ⟨hfLC2 1 (by norm_num), hdomLC2⟩
  · exact ⟨hfLC2 2 (by norm_num), hdomLC2⟩

theorem hframesC2 (dt : ℝ) : ∀ P ∈ leftProgsC2 dt, FramesMv P mvC2 := by
  intro P hP
  simp only [leftProgsC2, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgC2 dt d.2.2 mvC2 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hC204 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC202 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC201 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC2m05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC20 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC21 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC200 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC2m005 : Run.parseRat "-0.05" = some (-(1:ℚ)/20) := by
  have h : parseQ "-0.05" = some (⟨-5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC2025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC2075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC211 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC205 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC220 : Run.parseRat "2.0" = some (2) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC22 : Run.parseRat "2" = some (2) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC210 : Run.parseRat "1.0" = some (1) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC2m10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hC2m20 : Run.parseRat "-2.0" = some (-2) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hC2120 : Run.parseRat "12.0" = some (12) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstC22 (q : ℕ) : ℝ := if q = 0 then 2/5 else if q = 1 then 1/5 else 0

theorem fRC20_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRC2 q 0) x = x (Rv 2) := by
  interval_cases q <;>
    · simp [fRC2, hostDyn, mRC2, rover_coupled_IR, vsC2, Run.dynOf,
      Run.lowerE, hC204, hC202, hC20, hC21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRC21_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRC2 q 1) x = x (Rv 3) := by
  interval_cases q <;>
    · simp [fRC2, hostDyn, mRC2, rover_coupled_IR, vsC2, Run.dynOf,
      Run.lowerE, hC204, hC202, hC20, hC21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRC22_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRC2 q 2) x = cstC22 q := by
  interval_cases q <;>
    · simp [fRC2, hostDyn, mRC2, rover_coupled_IR, vsC2, Run.dynOf,
      Run.lowerE, hC204, hC202, hC20, hC21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstC22]
      try norm_num

theorem fRC23_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRC2 q 3) x = 0 := by
  interval_cases q <;>
    · simp [fRC2, hostDyn, mRC2, rover_coupled_IR, vsC2, Run.dynOf,
      Run.lowerE, hC204, hC202, hC20, hC21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num
theorem sat_domRC2 (x : State (Var 4)) : Formula.sat domRC2 x ↔
    (-(1:ℝ)/20 ≤ x (Rv 0) ∧ (1:ℝ)/4 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ (11:ℝ)/10) := by
  simp only [domRC2, hostEvolve, mRC2, rover_coupled_IR, vsC2]
  simp [Run.lowerF, Run.lowerE, hC2m005, hC2025, hC211, hC2m10,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

/-! ## The invariant's shape and the left-side extractors -/

theorem eval_gC2 (x : State (Var 4)) :
    Term.eval gC2 x = x (Lv 0) - (x (Rv 0) + 2) := by
  have hdL : ("L_px".drop 2).copy = "px" := by decide
  have hdR : ("R_px".drop 2).copy = "px" := by decide
  simp [gC2, gAt, atomsOf, invC2PF, rover_coupled_IR, Run.invToG, Run.lowerE, vsC2,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hC220,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem sat_domLC2 (x : State (Var 4)) : Formula.sat domLC2 x ↔
    (-(1:ℝ)/20 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 12 ∧ -(2:ℝ) ≤ x (Lv 1) ∧ x (Lv 1) ≤ 2 ∧
      -(1:ℝ)/20 ≤ x (Lv 2) ∧ x (Lv 2) ≤ 1 ∧ -(1:ℝ) ≤ x (Lv 3) ∧ x (Lv 3) ≤ 1) := by
  simp only [domLC2, hostEvolve, mLC2, rover_coupled_IR, vsC2]
  simp [Run.lowerF, Run.lowerE, hC2m005, hC2120, hC2m20, hC220, hC210, hC2m10,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  tauto

/-! ## Window facts specialized to the left position -/

theorem leftBlock_wf (fL : Fin 4 → Term (Var 4)) : (leftBlock fL).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 4)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 4).map hLinj

theorem htg_leftBlock (fL : Fin 4 → Term (Var 4)) : tgC2 ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
  exact aux_ne_Lv 1 i hi

theorem fLC20_eval (l : ℕ) (hl : l < 3) (x : State (Var 4)) :
    Term.eval (fLC2 l 0) x = x (Lv 2) := by
  interval_cases l <;>
    · simp [fLC2, hostDyn, mLC2, rover_coupled_IR, vsC2, Run.dynOf,
        Run.lowerE, hC202, hC201, hC2m05, hC20, hC21, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem window_pxL_bound (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (k : ℕ)
    {σ ν : State (Var 4)}
    (hsem : Program.sem (windowSeg (leftBlock (fLC2 l)) domLC2 tgC2 dt k) σ ν) :
    ν (Lv 0) ≤ σ (Lv 0) + (k : ℝ) * dt := by
  have hwfL := leftBlock_wf (fLC2 l)
  have htgb := htg_leftBlock (fLC2 l)
  have hbnd : ∀ x : State (Var 4), Formula.sat domLC2 x →
      Lie (DLCalTiming.clk tgC2 (leftBlock (fLC2 l)))
        (fun ω => Term.eval (Term.var (Lv 0)) ω) x ≤ 1 := by
    intro x hx
    have hfun : (fun ω : State (Var 4) => Term.eval (Term.var (Lv 0)) ω)
        = fun y => (1 : ℝ) * y (Lv 0) + 0 := by
      funext y; simp [Term.eval]
    rw [hfun, lie_affine_coord _ (clk_wellFormed tgC2 _ hwfL htgb) (Lv 0) 1 0 x]
    have hmem : ((Lv 0 : Var 4), fLC2 l 0) ∈ DLCalTiming.clk tgC2 (leftBlock (fLC2 l)) := by
      simp only [DLCalTiming.clk, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
    have hb : (Lv 0 : Var 4) ∈ (DLCalTiming.clk tgC2 (leftBlock (fLC2 l))).bound :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    have hfield : odeField (DLCalTiming.clk tgC2 (leftBlock (fLC2 l))) x (Lv 0)
        = Term.eval (fLC2 l 0) x := by
      simp only [odeField, if_pos hb]
      rw [ODESystem.rhs_eq_of_mem (clk_wellFormed tgC2 _ hwfL htgb) hmem]
    rw [hfield, fLC20_eval l hl]
    obtain ⟨-, -, -, -, -, h6, -, -⟩ := (sat_domLC2 x).mp hx
    linarith
  have hg := windowSeg_growth (leftBlock (fLC2 l)) domLC2 tgC2 dt k hwfL htgb
    (Term.var (Lv 0)) 1 (by norm_num)
    (by intro h; simp only [Term.fv, Set.mem_singleton_iff] at h;
        exact absurd h (by simp [tgC2, Lv, Prod.ext_iff])) hbnd hdt hsem
  simpa [Term.eval] using hg

theorem window_maskC2 (l : ℕ) (dt : ℝ) (k : ℕ)
    {σ ν : State (Var 4)}
    (hsem : Program.sem (windowSeg (leftBlock (fLC2 l)) domLC2 tgC2 dt k) σ ν) :
    ∀ j : Fin 4, ν (Rv j) = σ (Rv j) := by
  intro j
  refine windowSeg_mask (leftBlock (fLC2 l)) domLC2 tgC2 dt k (leftBlock_wf (fLC2 l))
    (htg_leftBlock (fLC2 l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC2 l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tgC2, Prod.ext_iff])

/-! ## The Safe hold run -/

/-- The Safe-mode hold: both velocities frozen, both positions linear — any
duration. Only `px` matters for the invariant; `py` rides along and the right
evolve domain never mentions it. -/
theorem sem_safe_hold (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 4)}
    (hdom : Formula.sat domRC2 μ) :
    Program.sem (Program.ode (rightBlock (fRC2 2) (Term.const 1)) domRC2) μ
      (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * τ
        else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * τ else μ x) := by
  have hR := (sat_domRC2 μ).mp hdom
  have hne10 : (Rv 1 : Var 4) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne20 : (Rv 2 : Var 4) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne21 : (Rv 2 : Var 4) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hne30 : (Rv 3 : Var 4) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne31 : (Rv 3 : Var 4) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  classical
  refine ⟨τ, fun t x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
      else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x,
    hτ, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp
    · by_cases h1 : x = Rv 1
      · subst h1; simp [if_neg hne10]
      · simp [if_neg h0, if_neg h1]
  · rfl
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRC2 2 ⟨0, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = μ (Rv 2) := by
        simp [Term.eval, AOp.interp, show fRC2 2 ⟨0, by norm_num⟩ = fRC2 2 0 from rfl,
          fRC20_eval 2 (by norm_num), if_neg hne20, if_neg hne21]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 0) + μ (Rv 2) * u)
          (μ (Rv 2) * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (μ (Rv 2))).const_add (μ (Rv 0))
      have heq : μ (Rv 2) * 1 = μ (Rv 2) := by ring
      rw [heq] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp
      · simp
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRC2 2 ⟨1, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = μ (Rv 3) := by
        simp [Term.eval, AOp.interp, show fRC2 2 ⟨1, by norm_num⟩ = fRC2 2 1 from rfl,
          fRC21_eval 2 (by norm_num), if_neg hne30, if_neg hne31]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 1) + μ (Rv 3) * u)
          (μ (Rv 3) * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (μ (Rv 3))).const_add (μ (Rv 1))
      have heq : μ (Rv 3) * 1 = μ (Rv 3) := by ring
      rw [heq] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [if_neg hne10]
      · simp [if_neg hne10]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRC2 2 ⟨2, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRC2 2 ⟨2, by norm_num⟩ = fRC2 2 2 from rfl,
          fRC22_eval 2 (by norm_num), cstC22]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 2))) ?_ ?_
      · intro y _; simp [if_neg hne20, if_neg hne21]
      · simp [if_neg hne20, if_neg hne21]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRC2 2 ⟨3, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRC2 2 ⟨3, by norm_num⟩ = fRC2 2 3 from rfl,
          fRC23_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 3))) ?_ ?_
      · intro y _; simp [if_neg hne30, if_neg hne31]
      · simp [if_neg hne30, if_neg hne31]
  · intro t ht x hx
    have hx0 : x ≠ Rv 0 := by
      intro h; subst h
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    have hx1 : x ≠ Rv 1 := by
      intro h; subst h
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨1, List.mem_finRange 1, rfl⟩)
    simp [if_neg hx0, if_neg hx1]
  · intro t ht
    rw [sat_domRC2]
    have ht0 : (0:ℝ) ≤ t := ht.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [eq_self_iff_true, if_true, if_pos rfl]
      have : 0 ≤ μ (Rv 2) * t := mul_nonneg (by linarith [hR.2.1]) ht0
      linarith [hR.1]
    · simp only [if_neg hne20, if_neg hne21]
      exact hR.2.1
    · simp only [if_neg hne20, if_neg hne21]
      exact hR.2.2.1
    · simp only [if_neg hne30, if_neg hne31]
      exact hR.2.2.2.1
    · simp only [if_neg hne30, if_neg hne31]
      exact hR.2.2.2.2

/-! ## The catch-up step provider — hops to Safe, one hold run, endpoint arithmetic -/

theorem HmultiC2 (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ P ∈ leftProgsC2 dt, ∀ (q : ℕ), q < GrC2.modes.length → ∀ σ, σ mvC2 = (q : ℝ) →
      Formula.sat (Formula.and (FM gC2 gsC2) envC2) σ →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrC2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrC2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gC2 gsC2) envC2)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrC2] using hq
  have hφ : σ (Lv 0) ≤ σ (Rv 0) + 2 := by
    have := (sat_FM_iff gC2 gsC2 σ).mp hσ.1 gC2 List.mem_cons_self
    rw [eval_gC2] at this
    linarith
  have hdomRσ : Formula.sat domRC2 σ := hσ.2.2
  have hRb := (sat_domRC2 σ).mp hdomRσ
  simp only [leftProgsC2, leftDataC2, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  -- the response is mode-path-to-Safe (zero-duration) plus one Safe hold of 8·dt
  have hchain2 : ∀ (a b c : ℕ × RMode (Var 4) × REdge (Var 4)),
      a.2.2.tgt = b.1 → b.2.2.tgt = c.1 →
      List.IsChain (fun x y => x.2.2.tgt = y.1) [a, b, c] := by
    intro a b c hab hbc
    refine (List.isChain_cons.mpr ⟨?_, ?_⟩)
    · intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hab
    · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hbc
  have hbuild : ∀ (l : ℕ), l < 3 → P = windowSeg (leftBlock (fLC2 l)) domLC2 tgC2 dt 2 →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrC2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrC2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gC2 gsC2) envC2)) σ := by
    intro l hl hPeq
    subst hPeq
    -- the faModal body, shared by all starts: the right survives the window,
    -- hops (zero-duration) to Safe, holds for 8·dt
    have hbody : ∀ (pres : List (Program (Var 4))),
        (∀ Q ∈ pres, ∀ μ : State (Var 4), Formula.sat domRC2 μ →
          Program.sem Q μ μ) →
        Formula.sat (faModal (Equiv.refl (Var 4))
          (windowSeg (leftBlock (fLC2 l)) domLC2 tgC2 dt 2)
          (bigSeq (pres ++ [Program.ode (rightBlock (fRC2 2) (Term.const 1)) domRC2]))
          (Formula.and (FM gC2 gsC2) envC2)) σ := by
      intro pres hpres
      rw [faModal_sat]
      intro ν hleft
      have hpx := window_pxL_bound l hl dt hdt 2 hleft
      push_cast at hpx
      have hmaskν := window_maskC2 l dt 2 hleft
      have hdomLν := windowSeg_end_domL (leftBlock (fLC2 l)) domLC2 tgC2 dt 2
        (by norm_num) hleft
      have hdomRν : Formula.sat domRC2 ν := by
        rw [sat_domRC2]
        rw [hmaskν 0, hmaskν 2, hmaskν 3]
        exact (sat_domRC2 σ).mp hdomRσ
      set τ : ℝ := 8 * dt with hτdef
      have hτ : 0 ≤ τ := by positivity
      have hhold := sem_safe_hold τ hτ hdomRν
      set μfin : State (Var 4) :=
        (fun x => if x = Rv 0 then ν (Rv 0) + ν (Rv 2) * τ
          else if x = Rv 1 then ν (Rv 1) + ν (Rv 3) * τ else ν x) with hμfin
      -- glue: pres are identity runs on ν, then the hold
      have hsemseq : Program.sem
          (bigSeq (pres ++ [Program.ode (rightBlock (fRC2 2) (Term.const 1)) domRC2]))
          ν μfin := by
        clear hpx
        induction pres with
        | nil =>
            simp only [List.nil_append, bigSeq]
            exact ⟨μfin, hhold, by rw [sem_test]; exact ⟨rfl, trivial⟩⟩
        | cons Q rest ih =>
            simp only [List.cons_append, bigSeq]
            refine ⟨ν, hpres Q List.mem_cons_self ν hdomRν, ?_⟩
            exact ih (fun Q' hQ' => hpres Q' (List.mem_cons_of_mem _ hQ'))
      refine ⟨μfin, by rw [Program.rename_refl]; exact hsemseq, ?_, ?_⟩
      · -- the invariant at the endpoint: catch-up arithmetic
        rw [sat_FM_iff]
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · rw [eval_gC2]
          have hν0 : μfin (Lv 0) = ν (Lv 0) := by
            simp [hμfin,
              if_neg (show (Lv 0 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
              if_neg (show (Lv 0 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
          have hνR : μfin (Rv 0) = ν (Rv 0) + ν (Rv 2) * τ := by simp [hμfin]
          rw [hν0, hνR]
          have hvfloor : (1:ℝ)/4 ≤ ν (Rv 2) := by
            rw [hmaskν 2]; exact hRb.2.1
          have hgain : 2 * dt ≤ ν (Rv 2) * τ := by
            rw [hτdef]
            nlinarith
          have hRν : ν (Rv 0) = σ (Rv 0) := hmaskν 0
          rw [hRν]
          linarith
        · exact absurd hg' (by simp [gsC2])
      · -- the environment at the endpoint
        constructor
        · -- domL: μfin agrees with ν on left coords
          have : Formula.sat domLC2 μfin := by
            rw [sat_domLC2]
            have h0 : μfin (Lv 0) = ν (Lv 0) := by
              simp [hμfin,
                if_neg (show (Lv 0 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 0 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h1 : μfin (Lv 1) = ν (Lv 1) := by
              simp [hμfin,
                if_neg (show (Lv 1 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 1 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h2 : μfin (Lv 2) = ν (Lv 2) := by
              simp [hμfin,
                if_neg (show (Lv 2 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 2 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h3 : μfin (Lv 3) = ν (Lv 3) := by
              simp [hμfin,
                if_neg (show (Lv 3 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 3 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            rw [h0, h1, h2, h3]
            exact (sat_domLC2 ν).mp hdomLν
          exact this
        · exact sem_ode_ends_in_domain hhold
    -- dispatch on the start mode: zero-hops up the chain, hold in Safe
    interval_cases q
    · refine ⟨[(0, modeC2 0, edgeC2 0 1), (1, modeC2 1, edgeC2 1 2), (2, modeC2 2, edgeC2 2 2)],
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrC2_modeAt 0 (by norm_num), edgeC2_mem 0 1 (by simp [GrC2])⟩
        · exact ⟨GrC2_modeAt 1 (by norm_num), edgeC2_mem 1 2 (by simp [GrC2])⟩
        · exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
      · exact hchain2 _ _ _ rfl rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRC2 0) (Term.const 1)) domRC2,
          Program.ode (rightBlock (fRC2 1) (Term.const 1)) domRC2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 0)
                (lam := Term.const 1) (domR := domRC2) hdom
              rwa [hρ] at hsem
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 1)
                (lam := Term.const 1) (domR := domRC2) hdom
              rwa [hρ] at hsem)
        simpa [modeC2] using this
    · refine ⟨[(1, modeC2 1, edgeC2 1 2), (2, modeC2 2, edgeC2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrC2_modeAt 1 (by norm_num), edgeC2_mem 1 2 (by simp [GrC2])⟩
        · exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
      · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
        intro y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRC2 1) (Term.const 1)) domRC2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            subst hQ
            obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 1)
              (lam := Term.const 1) (domR := domRC2) hdom
            rwa [hρ] at hsem)
        simpa [modeC2] using this
    · refine ⟨[(2, modeC2 2, edgeC2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl
        exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
      · simp
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [] (by intro Q hQ; exact absurd hQ (List.not_mem_nil))
        simpa [modeC2] using this
  rcases hP with rfl | rfl | rfl
  · exact hbuild 0 (by norm_num) rfl
  · exact hbuild 1 (by norm_num) rfl
  · exact hbuild 2 (by norm_num) rfl

/-- **`rover_coupled`, modal Theorem 3** — the CATCH-UP form at n = 4: the `py`/`vy`
coordinates are spectators (the right evolve domain never mentions `py`), so
the rover3_M1 argument transfers verbatim. The right's velocity floor
(`v_x ≥ 1/4` in its evolve domain) means a single Safe hold of duration `8·dt`
regains more position than the left window can gain (`windowSeg_growth` bounds
the left by `2·dt`), so the weakest declared tolerance (`Stop`, offset 2) is
re-established by endpoint arithmetic. Z3-free: NO verdict hypotheses at all. -/
theorem rover_coupled_modal (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsC2 dt))
      (rightAutomatonBody GrC2 mvC2)
      (RFormula.and (RFormula.and (canonInvM gC2 gsC2) (envLR domLC2 domRC2))
        (mvValidR mvC2 GrC2.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrC2 mvC2 (FM gC2 gsC2) domLC2 domRC2
    (leftProgsC2 dt) (canonInvM gC2 gsC2) (encode_canonInvM gC2 gsC2) ?_ ?_ ?_
  · exact hdis_multi GrC2 0 1 dt leftDataC2 (by decide) httC2 hRvC2 hLC2
  · exact hstep_assembled_multiF GrC2 mvC2 (FM gC2 gsC2) envC2 (leftProgsC2 dt)
      hmvFC2 hmvenvC2 hfreshC2 httC2 hltC2 (hframesC2 dt)
      (HmultiC2 dt hdt)
  · exact hddF_multiE GrC2 0 1 dt leftDataC2 (canonInvM gC2 gsC2) domLC2 domRC2
      (by decide) httC2 hRvC2 hLC2
      (canonInvM_varsL gC2 gsC2 (by
        intro g' hg'
        simp only [gC2, gsC2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gC2 gsC2) hdomLC2 hdomRC2

end RoverCoupledModal
end RelCertifier
