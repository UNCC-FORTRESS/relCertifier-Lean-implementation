/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `rover_position`, modal Theorem 3 (multiF, GENERATED)

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
import RelCertifier.Instances.BenchIR.rover_position

namespace RelCertifier
namespace RoverPositionModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 12800000

def vsP2 : List String := ["px", "py", "vx", "vy"]
def dummyP2 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLP2 (l : ℕ) : Parse.PMode := rover_position_IR.L.modes.getD l dummyP2
def mRP2 (q : ℕ) : Parse.PMode := rover_position_IR.R.modes.getD q dummyP2

abbrev mvP2 : Var 4 := (Side.Aux, 0)
abbrev aP2 : Fin 4 := (1 : Fin 4)
abbrev tgP2 : Var 4 := (Side.Aux, aP2)

noncomputable def fLP2 (l : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsP2 4 Side.L (mLP2 l)
noncomputable def fRP2 (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsP2 4 Side.R (mRP2 q)
noncomputable def domLP2 : Formula (Var 4) := hostEvolve vsP2 4 Side.L (mLP2 0)
noncomputable def domRP2 : Formula (Var 4) := hostEvolve vsP2 4 Side.R (mRP2 0)
noncomputable def envP2 : Formula (Var 4) := Formula.and domLP2 domRP2

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invP2PF : Parse.PForm :=
  (rover_position_IR.invariants.getD 2 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 4) :=
  ((Run.invToG vsP2 4 ((atomsOf invP2PF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gP2 : Term (Var 4) := gAt 0
noncomputable def gsP2 : List (Term (Var 4)) := []

/-! ## Side-splits -/

theorem fLP2_pipe (l : ℕ) (i : Fin 4) : fLP2 l i =
    (((some (mLP2 l)).bind (Run.dynOf vsP2 4 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRP2_pipe (q : ℕ) (i : Fin 4) : fRP2 q i =
    (((some (mRP2 q)).bind (Run.dynOf vsP2 4 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLP2_pipe : domLP2 =
    (((some (mLP2 0)).bind (fun m => Run.lowerF vsP2 4 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRP2_pipe : domRP2 =
    (((some (mRP2 0)).bind (fun m => Run.lowerF vsP2 4 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLP2 (l : ℕ) (hl : l < 3) : ∀ i, (fLP2 l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsP2) (some (mLP2 l))
    (by interval_cases l <;>
      simp [mLP2, rover_position_IR, Parse.PExpr.namesFree]) i x
    (fLP2_pipe l i ▸ hx))

theorem hfRP2 (q : ℕ) (hq : q < 3) : ∀ i, (fRP2 q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsP2) (some (mRP2 q))
    (by interval_cases q <;>
      simp [mRP2, rover_position_IR, Parse.PExpr.namesFree]) i x
    (fRP2_pipe q i ▸ hx))

theorem hdomLP2 : domLP2.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsP2) (some (mLP2 0))
    (by simp [mLP2, rover_position_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLP2_pipe ▸ hx))

theorem hdomRP2 : domRP2.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsP2) (some (mRP2 0))
    (by simp [mRP2, rover_position_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRP2_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gP2 :: gsP2, mvP2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gP2, gsP2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gP2 :: gsP2, tgP2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gP2, gsP2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFP2 : mvP2 ∉ (FM gP2 gsP2).fv := notMem_FM_fv hmvg
theorem htgFP2 : tgP2 ∉ (FM gP2 gsP2).fv := notMem_FM_fv htgg

theorem hmvenvP2 : mvP2 ∉ envP2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLP2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRP2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvP2 : tgP2 ∉ envP2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLP2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRP2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (one-way chain) -/

noncomputable def modeP2 (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRP2 q) (Term.const 1), dom := domRP2, weight := 1 }

def edgeP2 (st tgt : ℕ) : REdge (Var 4) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrP2 : SearchGraph (Var 4) :=
  { modes := [modeP2 0, modeP2 1, modeP2 2],
    edges := [edgeP2 0 1, edgeP2 0 0, edgeP2 1 2, edgeP2 1 1, edgeP2 2 2] }

theorem GrP2_modeAt (q : ℕ) (hq : q < 3) : GrP2.modeAt q = some (modeP2 q) := by
  interval_cases q <;> rfl

theorem httP2 : ∀ q, ∀ e ∈ GrP2.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrP2.edges := List.mem_of_mem_filter he
  simp only [GrP2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltP2 : ∀ q, ∀ e ∈ GrP2.edgesFrom q, e.tgt < GrP2.modes.length := by
  intro q e he
  have hmem : e ∈ GrP2.edges := List.mem_of_mem_filter he
  simp only [GrP2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrP2, edgeP2]

theorem hRvP2 : ∀ q m, GrP2.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeP2 q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP2] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP2] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP2] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrP2])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRP2 q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRP2 q) (Term.const 1) (hfRP2 q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRP2 hy

theorem edgeP2_mem : ∀ st tgt, edgeP2 st tgt ∈ GrP2.edges →
    edgeP2 st tgt ∈ GrP2.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeP2]⟩

theorem hfreshP2 : ∀ q m, GrP2.modeAt q = some m →
    mvP2 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvP2 q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataP2 : List ((Fin 4 → Term (Var 4)) × Formula (Var 4) × ℕ) :=
  [(fLP2 0, domLP2, 2), (fLP2 1, domLP2, 2), (fLP2 2, domLP2, 2)]

noncomputable def leftProgsP2 (dt : ℝ) : List (Program (Var 4)) :=
  leftDataP2.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgP2 dt d.2.2)

theorem hLP2 : ∀ d ∈ leftDataP2, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataP2, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLP2 0 (by norm_num), hdomLP2⟩
  · exact ⟨hfLP2 1 (by norm_num), hdomLP2⟩
  · exact ⟨hfLP2 2 (by norm_num), hdomLP2⟩

theorem hframesP2 (dt : ℝ) : ∀ P ∈ leftProgsP2 dt, FramesMv P mvP2 := by
  intro P hP
  simp only [leftProgsP2, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgP2 dt d.2.2 mvP2 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hP204 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP202 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP201 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP2m05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP20 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP21 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP200 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP2m005 : Run.parseRat "-0.05" = some (-(1:ℚ)/20) := by
  have h : parseQ "-0.05" = some (⟨-5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP2025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP2075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP211 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP205 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP220 : Run.parseRat "2.0" = some (2) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP22 : Run.parseRat "2" = some (2) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP210 : Run.parseRat "1.0" = some (1) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP2m10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hP2m20 : Run.parseRat "-2.0" = some (-2) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hP2120 : Run.parseRat "12.0" = some (12) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstP22 (q : ℕ) : ℝ := if q = 0 then 2/5 else if q = 1 then 1/5 else 0

theorem fRP20_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRP2 q 0) x = x (Rv 2) := by
  interval_cases q <;>
    · simp [fRP2, hostDyn, mRP2, rover_position_IR, vsP2, Run.dynOf,
      Run.lowerE, hP204, hP202, hP20, hP21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRP21_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRP2 q 1) x = x (Rv 3) := by
  interval_cases q <;>
    · simp [fRP2, hostDyn, mRP2, rover_position_IR, vsP2, Run.dynOf,
      Run.lowerE, hP204, hP202, hP20, hP21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRP22_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRP2 q 2) x = cstP22 q := by
  interval_cases q <;>
    · simp [fRP2, hostDyn, mRP2, rover_position_IR, vsP2, Run.dynOf,
      Run.lowerE, hP204, hP202, hP20, hP21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstP22]
      try norm_num

theorem fRP23_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRP2 q 3) x = 0 := by
  interval_cases q <;>
    · simp [fRP2, hostDyn, mRP2, rover_position_IR, vsP2, Run.dynOf,
      Run.lowerE, hP204, hP202, hP20, hP21, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num
theorem sat_domRP2 (x : State (Var 4)) : Formula.sat domRP2 x ↔
    (-(1:ℝ)/20 ≤ x (Rv 0) ∧ (1:ℝ)/4 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ (11:ℝ)/10) := by
  simp only [domRP2, hostEvolve, mRP2, rover_position_IR, vsP2]
  simp [Run.lowerF, Run.lowerE, hP2m005, hP2025, hP211, hP2m10,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

/-! ## The invariant's shape and the left-side extractors -/

theorem eval_gP2 (x : State (Var 4)) :
    Term.eval gP2 x = x (Lv 0) - (x (Rv 0) + 2) := by
  have hdL : ("L_px".drop 2).copy = "px" := by decide
  have hdR : ("R_px".drop 2).copy = "px" := by decide
  simp [gP2, gAt, atomsOf, invP2PF, rover_position_IR, Run.invToG, Run.lowerE, vsP2,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hP220,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem sat_domLP2 (x : State (Var 4)) : Formula.sat domLP2 x ↔
    (-(1:ℝ)/20 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 12 ∧ -(2:ℝ) ≤ x (Lv 1) ∧ x (Lv 1) ≤ 2 ∧
      -(1:ℝ)/20 ≤ x (Lv 2) ∧ x (Lv 2) ≤ 1 ∧ -(1:ℝ) ≤ x (Lv 3) ∧ x (Lv 3) ≤ 1) := by
  simp only [domLP2, hostEvolve, mLP2, rover_position_IR, vsP2]
  simp [Run.lowerF, Run.lowerE, hP2m005, hP2120, hP2m20, hP220, hP210, hP2m10,
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

theorem htg_leftBlock (fL : Fin 4 → Term (Var 4)) : tgP2 ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
  exact aux_ne_Lv 1 i hi

theorem fLP20_eval (l : ℕ) (hl : l < 3) (x : State (Var 4)) :
    Term.eval (fLP2 l 0) x = x (Lv 2) := by
  interval_cases l <;>
    · simp [fLP2, hostDyn, mLP2, rover_position_IR, vsP2, Run.dynOf,
        Run.lowerE, hP202, hP201, hP2m05, hP20, hP21, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem window_pxL_bound (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (k : ℕ)
    {σ ν : State (Var 4)}
    (hsem : Program.sem (windowSeg (leftBlock (fLP2 l)) domLP2 tgP2 dt k) σ ν) :
    ν (Lv 0) ≤ σ (Lv 0) + (k : ℝ) * dt := by
  have hwfL := leftBlock_wf (fLP2 l)
  have htgb := htg_leftBlock (fLP2 l)
  have hbnd : ∀ x : State (Var 4), Formula.sat domLP2 x →
      Lie (DLCalTiming.clk tgP2 (leftBlock (fLP2 l)))
        (fun ω => Term.eval (Term.var (Lv 0)) ω) x ≤ 1 := by
    intro x hx
    have hfun : (fun ω : State (Var 4) => Term.eval (Term.var (Lv 0)) ω)
        = fun y => (1 : ℝ) * y (Lv 0) + 0 := by
      funext y; simp [Term.eval]
    rw [hfun, lie_affine_coord _ (clk_wellFormed tgP2 _ hwfL htgb) (Lv 0) 1 0 x]
    have hmem : ((Lv 0 : Var 4), fLP2 l 0) ∈ DLCalTiming.clk tgP2 (leftBlock (fLP2 l)) := by
      simp only [DLCalTiming.clk, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
    have hb : (Lv 0 : Var 4) ∈ (DLCalTiming.clk tgP2 (leftBlock (fLP2 l))).bound :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    have hfield : odeField (DLCalTiming.clk tgP2 (leftBlock (fLP2 l))) x (Lv 0)
        = Term.eval (fLP2 l 0) x := by
      simp only [odeField, if_pos hb]
      rw [ODESystem.rhs_eq_of_mem (clk_wellFormed tgP2 _ hwfL htgb) hmem]
    rw [hfield, fLP20_eval l hl]
    obtain ⟨-, -, -, -, -, h6, -, -⟩ := (sat_domLP2 x).mp hx
    linarith
  have hg := windowSeg_growth (leftBlock (fLP2 l)) domLP2 tgP2 dt k hwfL htgb
    (Term.var (Lv 0)) 1 (by norm_num)
    (by intro h; simp only [Term.fv, Set.mem_singleton_iff] at h;
        exact absurd h (by simp [tgP2, Lv, Prod.ext_iff])) hbnd hdt hsem
  simpa [Term.eval] using hg

theorem window_maskP2 (l : ℕ) (dt : ℝ) (k : ℕ)
    {σ ν : State (Var 4)}
    (hsem : Program.sem (windowSeg (leftBlock (fLP2 l)) domLP2 tgP2 dt k) σ ν) :
    ∀ j : Fin 4, ν (Rv j) = σ (Rv j) := by
  intro j
  refine windowSeg_mask (leftBlock (fLP2 l)) domLP2 tgP2 dt k (leftBlock_wf (fLP2 l))
    (htg_leftBlock (fLP2 l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLP2 l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tgP2, Prod.ext_iff])

/-! ## The Safe hold run -/

/-- The Safe-mode hold: both velocities frozen, both positions linear — any
duration. Only `px` matters for the invariant; `py` rides along and the right
evolve domain never mentions it. -/
theorem sem_safe_hold (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 4)}
    (hdom : Formula.sat domRP2 μ) :
    Program.sem (Program.ode (rightBlock (fRP2 2) (Term.const 1)) domRP2) μ
      (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * τ
        else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * τ else μ x) := by
  have hR := (sat_domRP2 μ).mp hdom
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
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP2 2 ⟨0, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = μ (Rv 2) := by
        simp [Term.eval, AOp.interp, show fRP2 2 ⟨0, by norm_num⟩ = fRP2 2 0 from rfl,
          fRP20_eval 2 (by norm_num), if_neg hne20, if_neg hne21]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 0) + μ (Rv 2) * u)
          (μ (Rv 2) * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (μ (Rv 2))).const_add (μ (Rv 0))
      have heq : μ (Rv 2) * 1 = μ (Rv 2) := by ring
      rw [heq] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp
      · simp
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP2 2 ⟨1, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = μ (Rv 3) := by
        simp [Term.eval, AOp.interp, show fRP2 2 ⟨1, by norm_num⟩ = fRP2 2 1 from rfl,
          fRP21_eval 2 (by norm_num), if_neg hne30, if_neg hne31]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 1) + μ (Rv 3) * u)
          (μ (Rv 3) * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (μ (Rv 3))).const_add (μ (Rv 1))
      have heq : μ (Rv 3) * 1 = μ (Rv 3) := by ring
      rw [heq] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [if_neg hne10]
      · simp [if_neg hne10]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP2 2 ⟨2, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRP2 2 ⟨2, by norm_num⟩ = fRP2 2 2 from rfl,
          fRP22_eval 2 (by norm_num), cstP22]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 2))) ?_ ?_
      · intro y _; simp [if_neg hne20, if_neg hne21]
      · simp [if_neg hne20, if_neg hne21]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP2 2 ⟨3, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 2) * t
            else if x = Rv 1 then μ (Rv 1) + μ (Rv 3) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRP2 2 ⟨3, by norm_num⟩ = fRP2 2 3 from rfl,
          fRP23_eval 2 (by norm_num)]
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
    rw [sat_domRP2]
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

theorem HmultiP2 (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ P ∈ leftProgsP2 dt, ∀ (q : ℕ), q < GrP2.modes.length → ∀ σ, σ mvP2 = (q : ℝ) →
      Formula.sat (Formula.and (FM gP2 gsP2) envP2) σ →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrP2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrP2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gP2 gsP2) envP2)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrP2] using hq
  have hφ : σ (Lv 0) ≤ σ (Rv 0) + 2 := by
    have := (sat_FM_iff gP2 gsP2 σ).mp hσ.1 gP2 List.mem_cons_self
    rw [eval_gP2] at this
    linarith
  have hdomRσ : Formula.sat domRP2 σ := hσ.2.2
  have hRb := (sat_domRP2 σ).mp hdomRσ
  simp only [leftProgsP2, leftDataP2, List.map_cons, List.map_nil, List.mem_cons,
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
  have hbuild : ∀ (l : ℕ), l < 3 → P = windowSeg (leftBlock (fLP2 l)) domLP2 tgP2 dt 2 →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrP2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrP2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gP2 gsP2) envP2)) σ := by
    intro l hl hPeq
    subst hPeq
    -- the faModal body, shared by all starts: the right survives the window,
    -- hops (zero-duration) to Safe, holds for 8·dt
    have hbody : ∀ (pres : List (Program (Var 4))),
        (∀ Q ∈ pres, ∀ μ : State (Var 4), Formula.sat domRP2 μ →
          Program.sem Q μ μ) →
        Formula.sat (faModal (Equiv.refl (Var 4))
          (windowSeg (leftBlock (fLP2 l)) domLP2 tgP2 dt 2)
          (bigSeq (pres ++ [Program.ode (rightBlock (fRP2 2) (Term.const 1)) domRP2]))
          (Formula.and (FM gP2 gsP2) envP2)) σ := by
      intro pres hpres
      rw [faModal_sat]
      intro ν hleft
      have hpx := window_pxL_bound l hl dt hdt 2 hleft
      push_cast at hpx
      have hmaskν := window_maskP2 l dt 2 hleft
      have hdomLν := windowSeg_end_domL (leftBlock (fLP2 l)) domLP2 tgP2 dt 2
        (by norm_num) hleft
      have hdomRν : Formula.sat domRP2 ν := by
        rw [sat_domRP2]
        rw [hmaskν 0, hmaskν 2, hmaskν 3]
        exact (sat_domRP2 σ).mp hdomRσ
      set τ : ℝ := 8 * dt with hτdef
      have hτ : 0 ≤ τ := by positivity
      have hhold := sem_safe_hold τ hτ hdomRν
      set μfin : State (Var 4) :=
        (fun x => if x = Rv 0 then ν (Rv 0) + ν (Rv 2) * τ
          else if x = Rv 1 then ν (Rv 1) + ν (Rv 3) * τ else ν x) with hμfin
      -- glue: pres are identity runs on ν, then the hold
      have hsemseq : Program.sem
          (bigSeq (pres ++ [Program.ode (rightBlock (fRP2 2) (Term.const 1)) domRP2]))
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
        · rw [eval_gP2]
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
        · exact absurd hg' (by simp [gsP2])
      · -- the environment at the endpoint
        constructor
        · -- domL: μfin agrees with ν on left coords
          have : Formula.sat domLP2 μfin := by
            rw [sat_domLP2]
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
            exact (sat_domLP2 ν).mp hdomLν
          exact this
        · exact sem_ode_ends_in_domain hhold
    -- dispatch on the start mode: zero-hops up the chain, hold in Safe
    interval_cases q
    · refine ⟨[(0, modeP2 0, edgeP2 0 1), (1, modeP2 1, edgeP2 1 2), (2, modeP2 2, edgeP2 2 2)],
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrP2_modeAt 0 (by norm_num), edgeP2_mem 0 1 (by simp [GrP2])⟩
        · exact ⟨GrP2_modeAt 1 (by norm_num), edgeP2_mem 1 2 (by simp [GrP2])⟩
        · exact ⟨GrP2_modeAt 2 (by norm_num), edgeP2_mem 2 2 (by simp [GrP2])⟩
      · exact hchain2 _ _ _ rfl rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRP2 0) (Term.const 1)) domRP2,
          Program.ode (rightBlock (fRP2 1) (Term.const 1)) domRP2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP2 0)
                (lam := Term.const 1) (domR := domRP2) hdom
              rwa [hρ] at hsem
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP2 1)
                (lam := Term.const 1) (domR := domRP2) hdom
              rwa [hρ] at hsem)
        simpa [modeP2] using this
    · refine ⟨[(1, modeP2 1, edgeP2 1 2), (2, modeP2 2, edgeP2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrP2_modeAt 1 (by norm_num), edgeP2_mem 1 2 (by simp [GrP2])⟩
        · exact ⟨GrP2_modeAt 2 (by norm_num), edgeP2_mem 2 2 (by simp [GrP2])⟩
      · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
        intro y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRP2 1) (Term.const 1)) domRP2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            subst hQ
            obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP2 1)
              (lam := Term.const 1) (domR := domRP2) hdom
            rwa [hρ] at hsem)
        simpa [modeP2] using this
    · refine ⟨[(2, modeP2 2, edgeP2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl
        exact ⟨GrP2_modeAt 2 (by norm_num), edgeP2_mem 2 2 (by simp [GrP2])⟩
      · simp
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [] (by intro Q hQ; exact absurd hQ (List.not_mem_nil))
        simpa [modeP2] using this
  rcases hP with rfl | rfl | rfl
  · exact hbuild 0 (by norm_num) rfl
  · exact hbuild 1 (by norm_num) rfl
  · exact hbuild 2 (by norm_num) rfl

/-- **`rover_position`, modal Theorem 3** — the CATCH-UP form at n = 4: the `py`/`vy`
coordinates are spectators (the right evolve domain never mentions `py`), so
the rover3_M1 argument transfers verbatim. The right's velocity floor
(`v_x ≥ 1/4` in its evolve domain) means a single Safe hold of duration `8·dt`
regains more position than the left window can gain (`windowSeg_growth` bounds
the left by `2·dt`), so the weakest declared tolerance (`Stop`, offset 2) is
re-established by endpoint arithmetic. Z3-free: NO verdict hypotheses at all. -/
theorem rover_position_modal (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsP2 dt))
      (rightAutomatonBody GrP2 mvP2)
      (RFormula.and (RFormula.and (canonInvM gP2 gsP2) (envLR domLP2 domRP2))
        (mvValidR mvP2 GrP2.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrP2 mvP2 (FM gP2 gsP2) domLP2 domRP2
    (leftProgsP2 dt) (canonInvM gP2 gsP2) (encode_canonInvM gP2 gsP2) ?_ ?_ ?_
  · exact hdis_multi GrP2 0 1 dt leftDataP2 (by decide) httP2 hRvP2 hLP2
  · exact hstep_assembled_multiF GrP2 mvP2 (FM gP2 gsP2) envP2 (leftProgsP2 dt)
      hmvFP2 hmvenvP2 hfreshP2 httP2 hltP2 (hframesP2 dt)
      (HmultiP2 dt hdt)
  · exact hddF_multiE GrP2 0 1 dt leftDataP2 (canonInvM gP2 gsP2) domLP2 domRP2
      (by decide) httP2 hRvP2 hLP2
      (canonInvM_varsL gP2 gsP2 (by
        intro g' hg'
        simp only [gP2, gsP2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gP2 gsP2) hdomLP2 hdomRP2

end RoverPositionModal
end RelCertifier
