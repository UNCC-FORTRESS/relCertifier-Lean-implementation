/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `rover_dof_terrain_rung2`, modal Theorem 3 (multiF at n = 6)

The multiF pilot's exact cover shape (three λ = 1, k = 1 windows on the one-way
terrain chain, two-component tolerance `v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`, climb
dispatch) at six coordinates: the right adds a decaying attitude row
(`ψ' = −ψ`, two more strict faces) and three zero-field rows (`z`, `θ`, `φ` —
six more zero-Lie non-strict faces). Existence stays Z3-free (`K = 3`, `L = 8`).

Residuals: six stratified-DC packs (`VerdT l m`, two queries each), the same
certified-pair table as the pilot. Axioms: the standard three +
`z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung2

namespace RelCertifier
namespace RoverDofTerrainRung2Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsT : List String := ["v", "s", "psi", "z", "theta_p", "phi_r"]
def dummyT : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLT (l : ℕ) : Parse.PMode := rover_dof_terrain_rung2_IR.L.modes.getD l dummyT
def mRT (q : ℕ) : Parse.PMode := rover_dof_terrain_rung2_IR.R.modes.getD q dummyT

abbrev mvT : Var 6 := (Side.Aux, 0)
abbrev aT : Fin 6 := (1 : Fin 6)
abbrev tgT : Var 6 := (Side.Aux, aT)

noncomputable def fLT (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsT 6 Side.L (mLT l)
noncomputable def fRT (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsT 6 Side.R (mRT q)
noncomputable def domLT : Formula (Var 6) := hostEvolve vsT 6 Side.L (mLT 0)
noncomputable def domRT : Formula (Var 6) := hostEvolve vsT 6 Side.R (mRT 0)
noncomputable def envT : Formula (Var 6) := Formula.and domLT domRT

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invTPF : Parse.PForm :=
  (rover_dof_terrain_rung2_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 6) :=
  ((Run.invToG vsT 6 ((atomsOf invTPF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gT : Term (Var 6) := gAt 0
noncomputable def gsT : List (Term (Var 6)) := [gAt 1]

/-! ## Side-splits -/

theorem fLT_pipe (l : ℕ) (i : Fin 6) : fLT l i =
    (((some (mLT l)).bind (Run.dynOf vsT 6 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRT_pipe (q : ℕ) (i : Fin 6) : fRT q i =
    (((some (mRT q)).bind (Run.dynOf vsT 6 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLT_pipe : domLT =
    (((some (mLT 0)).bind (fun m => Run.lowerF vsT 6 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRT_pipe : domRT =
    (((some (mRT 0)).bind (fun m => Run.lowerF vsT 6 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLT (l : ℕ) (hl : l < 3) : ∀ i, (fLT l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsT) (some (mLT l))
    (by interval_cases l <;>
      simp [mLT, rover_dof_terrain_rung2_IR, Parse.PExpr.namesFree]) i x
    (fLT_pipe l i ▸ hx))

theorem hfRT (q : ℕ) (hq : q < 3) : ∀ i, (fRT q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsT) (some (mRT q))
    (by interval_cases q <;>
      simp [mRT, rover_dof_terrain_rung2_IR, Parse.PExpr.namesFree]) i x
    (fRT_pipe q i ▸ hx))

theorem hdomLT : domLT.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsT) (some (mLT 0))
    (by simp [mLT, rover_dof_terrain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLT_pipe ▸ hx))

theorem hdomRT : domRT.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsT) (some (mRT 0))
    (by simp [mRT, rover_dof_terrain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRT_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gT :: gsT, mvT ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gT, gsT, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gT :: gsT, tgT ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gT, gsT, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFT : mvT ∉ (FM gT gsT).fv := notMem_FM_fv hmvg
theorem htgFT : tgT ∉ (FM gT gsT).fv := notMem_FM_fv htgg

theorem hmvenvT : mvT ∉ envT.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLT h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRT h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvT : tgT ∉ envT.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLT h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRT h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph -/

noncomputable def modeT (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fRT q) (Term.const 1), dom := domRT, weight := 1 }

def edgeT (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrT : SearchGraph (Var 6) :=
  { modes := [modeT 0, modeT 1, modeT 2],
    edges := [edgeT 0 1, edgeT 0 0, edgeT 1 2, edgeT 1 1, edgeT 2 2] }

theorem GrT_modeAt (q : ℕ) (hq : q < 3) : GrT.modeAt q = some (modeT q) := by
  interval_cases q <;> rfl

theorem httT : ∀ q, ∀ e ∈ GrT.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrT.edges := List.mem_of_mem_filter he
  simp only [GrT, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltT : ∀ q, ∀ e ∈ GrT.edgesFrom q, e.tgt < GrT.modes.length := by
  intro q e he
  have hmem : e ∈ GrT.edges := List.mem_of_mem_filter he
  simp only [GrT, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrT, edgeT]

theorem hRvT : ∀ q m, GrT.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeT q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrT] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrT] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrT] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrT])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRT q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRT q) (Term.const 1) (hfRT q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRT hy

theorem edgeT_mem : ∀ st tgt, edgeT st tgt ∈ GrT.edges →
    edgeT st tgt ∈ GrT.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeT]⟩

theorem hfreshT : ∀ q m, GrT.modeAt q = some m →
    mvT ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvT q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataT : List ((Fin 6 → Term (Var 6)) × Formula (Var 6) × ℕ) :=
  [(fLT 0, domLT, 1), (fLT 1, domLT, 1), (fLT 2, domLT, 1)]

noncomputable def leftProgsT (dt : ℝ) : List (Program (Var 6)) :=
  leftDataT.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgT dt d.2.2)

theorem hLT : ∀ d ∈ leftDataT, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataT, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLT 0 (by norm_num), hdomLT⟩
  · exact ⟨hfLT 1 (by norm_num), hdomLT⟩
  · exact ⟨hfLT 2 (by norm_num), hdomLT⟩

theorem hframesT (dt : ℝ) : ∀ P ∈ leftProgsT dt, FramesMv P mvT := by
  intro P hP
  simp only [leftProgsT, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgT dt d.2.2 mvT (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem ht030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem htm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem ht0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem ht00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem ht08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem htm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem ht06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem htm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem ht11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Field and shape pins -/

noncomputable def cstT (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRT0_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 0) x = 3 * (cstT q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cstT]

theorem fRT1_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRT2_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRT3_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 3) x = 0 := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRT4_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 4) x = 0 := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRT5_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRT q 5) x = 0 := by
  interval_cases q <;>
    simp [fRT, hostDyn, mRT, rover_dof_terrain_rung2_IR, vsT, Run.dynOf,
      Run.lowerE, ht3, ht030, ht050, ht065, htm1, ht0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRT (x : State (Var 6)) : Formula.sat domRT x ↔
    (-(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3/5 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ 11/10) := by
  simp only [domRT, hostEvolve, mRT, rover_dof_terrain_rung2_IR, vsT]
  simp [Run.lowerF, Run.lowerE, htm05, ht06, ht015, ht00, ht08, htm10, ht11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

theorem gAt0_eval (x : State (Var 6)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invTPF, rover_dof_terrain_rung2_IR, Run.invToG,
    Run.lowerE, vsT, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 6)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invTPF, rover_dof_terrain_rung2_IR, Run.invToG,
    Run.lowerE, vsT, ht02, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-! ## Existence -/

noncomputable def faceVLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))
noncomputable def facePsiLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 2))
noncomputable def facePsiHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 2)) (Term.const ((3:ℝ)/20))
noncomputable def faceSLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))
noncomputable def faceZLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 3))
noncomputable def faceZHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 3)) (Term.const ((11:ℝ)/10))
noncomputable def faceThLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 4))
noncomputable def faceThHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 4)) (Term.const ((3:ℝ)/5))
noncomputable def facePhLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 5))
noncomputable def facePhHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 5)) (Term.const ((3:ℝ)/5))

noncomputable def gsST : List (Term (Var 6)) := [faceVLo, faceVHi, facePsiLo, facePsiHi]
noncomputable def gsNT : List (Term (Var 6)) :=
  [faceSLo, faceZLo, faceZHi, faceThLo, faceThHi, facePhLo, facePhHi]

theorem faces_fv_RT : ∀ gT' ∈ gsST ++ gsNT, ∀ x ∈ gT'.fv, x ∈ range Rv := by
  intro gT' hgT x hx
  simp only [gsST, gsNT, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, facePsiLo, facePsiHi, faceSLo, faceZLo, faceZHi,
        faceThLo, faceThHi, facePhLo, facePhHi, Term.fv, Set.mem_union,
        Set.mem_empty_iff_false, false_or, or_false, Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

theorem odeField_RT (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    odeField (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cstT q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0)
        else if c = Rv 2 then -1 * x (Rv 2)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have h0 : (Lv j : Var 6) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      have h1 : (Lv j : Var 6) ≠ Rv 1 := by simp [Lv, Rv, Prod.ext_iff]
      have h2 : (Lv j : Var 6) ≠ Rv 2 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, h0, h1, h2]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRT0_eval q hq]
      · have h0 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRT1_eval q hq, h0]
      · have h0 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRT2_eval q hq, h0, h1]
      · have h0 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRT3_eval q hq, h0, h1, h2]
      · have h0 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRT4_eval q hq, h0, h1, h2]
      · have h0 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRT5_eval q hq, h0, h1, h2]
  · have hnotR : ∀ j : Fin 6, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1),
      if_neg (hnotR 2)]

theorem hbndS_T (q : ℕ) (hq : q < 3) : ∀ gT' ∈ gsST, ∀ x : State (Var 6),
    Term.eval gT' x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1))
      (fun ω => Term.eval gT' ω) x < 0 := by
  have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  intro gT' hgT x hface
  simp only [gsST, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl
  · have hx0 : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
      odeField_RT q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstT]
  · have hx0 : x (Rv 0) = 4/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-(4/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(4/5)) x,
      odeField_RT q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstT]
  · have hx2 : x (Rv 2) = -(1:ℝ)/2 := by
      simp only [facePsiLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval facePsiLo ω)
        = fun y => (-1 : ℝ) * y (Rv 2) + (-(1/2)) := by
      funext y; simp [facePsiLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) (-1) (-(1/2)) x,
      odeField_RT q hq]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, hx2]
    norm_num
  · have hx2 : x (Rv 2) = (3:ℝ)/20 := by
      simp only [facePsiHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval facePsiHi ω)
        = fun y => (1 : ℝ) * y (Rv 2) + (-(3/20)) := by
      funext y; simp [facePsiHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) 1 (-(3/20)) x,
      odeField_RT q hq]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, hx2]
    norm_num

theorem hbndN_T (q : ℕ) (hq : q < 3) : ∀ i (hi : i < gsNT.length), ∀ x : State (Var 6),
    (∀ gT' ∈ gsST ++ ([] : List (Term (Var 6))), Term.eval gT' x ≤ 0) →
    Lie (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1))
      (fun ω => Term.eval gsNT[i] ω) x ≤ 0 := by
  have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hz0 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hz1 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hz2 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  have hth0 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hth1 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hth2 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  have hph0 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hph1 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hph2 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  intro i hi x hx
  have hi7 : i < 7 := by simpa [gsNT] using hi
  have hv0 : 0 ≤ x (Rv 0) := by
    have := hx faceVLo (List.mem_append_left _ (by simp [gsST]))
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  interval_cases i
  · show Lie _ (fun ω => Term.eval faceSLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceSLo ω)
        = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [faceSLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
      odeField_RT q hq]
    simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl]
    linarith
  · show Lie _ (fun ω => Term.eval faceZLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceZLo ω)
        = fun y => (-1 : ℝ) * y (Rv 3) + (-1) := by
      funext y; simp [faceZLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) (-1) (-1) x,
      odeField_RT q hq]
    simp only [if_neg hz0, if_neg hz1, if_neg hz2]
    norm_num
  · show Lie _ (fun ω => Term.eval faceZHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceZHi ω)
        = fun y => (1 : ℝ) * y (Rv 3) + (-(11/10)) := by
      funext y; simp [faceZHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) 1 (-(11/10)) x,
      odeField_RT q hq]
    simp only [if_neg hz0, if_neg hz1, if_neg hz2]
    norm_num
  · show Lie _ (fun ω => Term.eval faceThLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 4) + (-(1/2)) := by
      funext y; simp [faceThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) (-1) (-(1/2)) x,
      odeField_RT q hq]
    simp only [if_neg hth0, if_neg hth1, if_neg hth2]
    norm_num
  · show Lie _ (fun ω => Term.eval faceThHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceThHi ω)
        = fun y => (1 : ℝ) * y (Rv 4) + (-(3/5)) := by
      funext y; simp [faceThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) 1 (-(3/5)) x,
      odeField_RT q hq]
    simp only [if_neg hth0, if_neg hth1, if_neg hth2]
    norm_num
  · show Lie _ (fun ω => Term.eval facePhLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval facePhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 5) + (-(1/2)) := by
      funext y; simp [facePhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) (-1) (-(1/2)) x,
      odeField_RT q hq]
    simp only [if_neg hph0, if_neg hph1, if_neg hph2]
    norm_num
  · show Lie _ (fun ω => Term.eval facePhHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval facePhHi ω)
        = fun y => (1 : ℝ) * y (Rv 5) + (-(3/5)) := by
      funext y; simp [facePhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) 1 (-(3/5)) x,
      odeField_RT q hq]
    simp only [if_neg hph0, if_neg hph1, if_neg hph2]
    norm_num

theorem hLip_T (q : ℕ) (hq : q < 3) (ν : State (Var 6)) :
    LipschitzOnWith 3 (odeField (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RT q hq, odeField_RT q hq]
  have hdc : ∀ j : Fin 6, |x (Rv j) - y (Rv j)| ≤ dist x y := by
    intro j
    have h := dist_le_pi_dist x y (Rv j)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  have hcoe : ((3 : NNReal) : ℝ) = 3 := rfl
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : 3 * (cstT q - x (Rv 0)) - 3 * (cstT q - y (Rv 0))
        = -3 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have habs : |(-3 : ℝ)| = 3 := by norm_num
    rw [habs, hcoe]
    nlinarith [hdc 0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    nlinarith [hdc 0, abs_nonneg (x (Rv 0) - y (Rv 0))]
  by_cases hc2 : c = Rv 2
  · subst hc2
    have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h20, if_neg h21, eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    have hdiff : -1 * x (Rv 2) - -1 * y (Rv 2) = -(x (Rv 2) - y (Rv 2)) := by ring
    rw [hdiff, abs_neg]
    nlinarith [hdc 2]
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2]
    rw [hcoe]
    simp [dist_nonneg]

theorem hfbnd_T (q : ℕ) (hq : q < 3) (ν : State (Var 6))
    (hν : ∀ gT' ∈ gsST, Term.eval gT' ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRT q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  intro x hx
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsST])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν8 : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsST])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hν2l : -(1:ℝ)/2 ≤ ν (Rv 2) := by
    have := hν facePsiLo (by simp [gsST])
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hν2h : ν (Rv 2) ≤ 3/20 := by
    have := hν facePsiHi (by simp [gsST])
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  rw [Metric.mem_closedBall] at hx
  have hcb : ∀ j : Fin 6, |x (Rv j) - ν (Rv j)| ≤ 1 := by
    intro j
    have h := dist_le_pi_dist x ν (Rv j)
    rw [Real.dist_eq] at h
    linarith
  have hx0 : |x (Rv 0)| ≤ 9/5 := by
    have h := hcb 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν8⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hx2 : |x (Rv 2)| ≤ 3/2 := by
    have h := hcb 2
    have hνb : |ν (Rv 2)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 2)) (ν (Rv 2))
    linarith [abs_le.mp hνb]
  rw [odeField_RT q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cstT q ∧ cstT q ≤ 13/20 := by
      interval_cases q <;> norm_num [cstT]
    rw [abs_le]
    push_cast
    obtain ⟨hc1, hc2⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hx0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    push_cast
    linarith [abs_le.mp hx0]
  by_cases hc2 : c = Rv 2
  · subst hc2
    have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h20, if_neg h21, eq_self_iff_true, if_true, if_pos rfl,
      Real.norm_eq_abs]
    push_cast
    have hdiff : |(-1 : ℝ) * x (Rv 2)| = |x (Rv 2)| := by
      rw [abs_mul]; norm_num
    rw [hdiff]
    linarith [abs_le.mp hx2]
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2]
    norm_num

theorem esT (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM gT gsT) envT) σ →
      HExistSegB (fLT l) (fRT m) (Term.const 1) domLT domRT dt
        (Function.update σ tgT 0) := by
  intro σ hσ
  have hR : Formula.sat domRT σ := hσ.2.2
  rw [sat_domRT] at hR
  obtain ⟨h5l, h5h, h2l, h2h, h1l, h4l, h4h, h0l, h0h, h3l, h3h⟩ := hR
  have hupd : ∀ j : Fin 6, σ (Side.R, j) = Function.update σ tgT 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgT, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsST, Term.eval gT' (Function.update σ tgT 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsST, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNT, Term.eval gT' (Function.update σ tgT 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNT, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratified (fLT l) (fRT m) (Term.const 1)
    domLT domRT gsST [] gsNT 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLT l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RT gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLT l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RT gT' (List.mem_append_right _ hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x _ hface
      exact hbndS_T m hm gT' hgT x hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      exact hbndN_T m hm i hi x hx)
    (by
      intro x hS hN
      have hS' : ∀ gT' ∈ gsST, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hv0 : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsST])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hv8 : x (Rv 0) ≤ 4/5 := by
        have := hS' faceVHi (by simp [gsST])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsST])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hp2 : x (Rv 2) ≤ 3/20 := by
        have := hS' facePsiHi (by simp [gsST])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have hs0 : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNT])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hz1 : -(1:ℝ) ≤ x (Rv 3) := by
        have := hN faceZLo (by simp [gsNT])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hz2 : x (Rv 3) ≤ 11/10 := by
        have := hN faceZHi (by simp [gsNT])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have ht1 : -(1:ℝ)/2 ≤ x (Rv 4) := by
        have := hN faceThLo (by simp [gsNT])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have ht2 : x (Rv 4) ≤ 3/5 := by
        have := hN faceThHi (by simp [gsNT])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hf1 : -(1:ℝ)/2 ≤ x (Rv 5) := by
        have := hN facePhLo (by simp [gsNT])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hf2 : x (Rv 5) ≤ 3/5 := by
        have := hN facePhHi (by simp [gsNT])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      exact (sat_domRT x).mpr ⟨hf1, hf2, hp1, hp2, hs0, ht1, ht2, hv0, hv8, hz1, hz2⟩)
    3 8 1 one_pos
    (fun ν0 _ => hLip_T m hm ν0)
    (fun ν0 h0 => hfbnd_T m hm ν0 (fun gT' hgT => h0 gT' (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgT 0)
    hfS
    hfN
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The route verdicts (stratified-DC over the two components) -/

def VerdT (l m : ℕ) : Prop :=
  ∀ i (hi : i < (gT :: gsT).length),
    z3solve (flowQuery ⟨(gT :: gsT)[i], fLT l, fRT m, Term.const 1,
      strataDomHost (Formula.and domLT domRT) ((gT :: gsT).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gT :: gsT)[i], fLT l, fRT m, Term.const 1,
      strataDomHost (Formula.and domLT domRT) ((gT :: gsT).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gT :: gsT)[i], fLT l, fRT m, Term.const 1,
      strataDomHost (Formula.and domLT domRT) ((gT :: gsT).take i)⟩) = Verdict.unsat

/-! ## The certified couplings -/

theorem coupleT (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdT l m) :
    ∀ σ', Formula.sat (Formula.and (FM gT gsT) envT) σ' → σ' tgT = 0 →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tgT (leftBlock (fLT l))) domLT)
        (Program.ode (rightBlock (fRT m) (Term.const 1)) domRT)
        (Formula.and (FM gT gsT) envT) tgT dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgT (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgT
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLT l) (fRT m) (Term.const 1)
    (Formula.and domLT domRT) (gT :: gsT) hv
  have hboxes : ∀ g' ∈ gT :: gsT, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLT l) ++ rightBlock (fRT m) (Term.const 1))
      (Formula.and domLT domRT)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gT gsT σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gT gsT (fLT l) (fRT m)
    (Term.const 1) domLT domRT tgT dt
    (LR_blocks_disjoint _ _ _ (hfLT l hl) (hfRT m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLT hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRT hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLT l) _ h
      exact aux_ne_Lv aT i hi)
    (fun h => aux_notin_range_Lv aT (leftBlock_readVars_sub (fLT l) (hfLT l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRT m) (Term.const 1) _ h
      exact aux_ne_Rv aT i hi)
    (fun h => aux_notin_range_Rv aT (rightBlock_readVars_sub (fRT m) (Term.const 1)
      (hfRT m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aT (rightBlock_boundSet_sub (fRT m) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aT (hdomLT h))
    (fun h => aux_notin_range_Rv aT (hdomRT h))
    htgg hboxes
    (esT l m hl hm dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLT ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRT μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLT μ := by
    rwa [(Formula.coincidence domLT (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLT hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRT m) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLT μ ↔ Formula.sat domLT ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Static hops and the window response -/

theorem static_hopT (fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6))
    (φ : Formula (Var 6)) (σ : State (Var 6)) (hσφ : Formula.sat φ σ)
    (hdom : Formula.sat (Formula.and domLT domRT) σ) :
    ∃ ρ, Program.sem ((⟨fR, lam, domRT⟩ : RepoHop 6).prog domLT) σ ρ
      ∧ Formula.sat φ ρ := by
  refine ⟨σ, ⟨0, fun _ => σ, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩, hσφ⟩
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
    exact hdom

theorem hops_convT : ∀ (ps : List ℕ), (∀ p ∈ ps, p < 3) →
    List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ → Program.sem q ν μ)
      (ps.map (fun p => (⟨fRT p, Term.const 1, domRT⟩ : RepoHop 6).prog domLT))
      (ps.map (fun p => Program.ode (rightBlock (fRT p) (Term.const 1)) domRT)) := by
  intro ps
  induction ps with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hps
      refine List.Forall₂.cons ?_ (ih (fun p hp => hps p (List.mem_cons_of_mem a hp)))
      intro ν μ hrun
      exact joint_run_toR (hfRT a (hps a List.mem_cons_self)) (by simp [Term.fv]) hrun

/-- The window response: static hops up the chain, the certified coupling at the
reached mode. -/
theorem respondT (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdT l m) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FM gT gsT) envT) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (windowSeg (leftBlock (fLT l)) domLT tgT dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRT p) (Term.const 1))
          domRT))
        ++ [Program.ode (rightBlock (fRT m) (Term.const 1)) domRT]))
      (Formula.and (FM gT gsT) envT)) σ := by
  have hfa := Hmulti_window1_prefixedF (fLT l) domLT (FM gT gsT) envT aT dt
    htgFT htgenvT
    (path.map (fun p => (⟨fRT p, Term.const 1, domRT⟩ : RepoHop 6)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRT p (hpath p hp), by simp [Term.fv], hdomRT⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact static_hopT (fRT p) (Term.const 1) _ σ' hσ' hσ'.2)
    (hfLT l hl) hdomLT
    (Program.ode (rightBlock (fRT m) (Term.const 1)) domRT)
    (coupleT l m hl hm dt hdt hv)
    hσ
  rw [show (path.map (fun p => (⟨fRT p, Term.const 1, domRT⟩ : RepoHop 6))).map
      (fun h => h.prog domLT)
      = path.map (fun p => (⟨fRT p, Term.const 1, domRT⟩ : RepoHop 6).prog domLT)
    from by rw [List.map_map]; rfl] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono
    (List.rel_append (hops_convT path hpath)
      (List.Forall₂.cons (fun _ _ h => h) List.Forall₂.nil)) ν μ hrun) hfa

/-! ## The step provider (in-place at or ahead, climb from behind) -/

theorem HmultiT (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdT 0 0) (hv01 : VerdT 0 1) (hv02 : VerdT 0 2)
    (hv11 : VerdT 1 1) (hv12 : VerdT 1 2) (hv22 : VerdT 2 2) :
    ∀ P ∈ leftProgsT dt, ∀ (q : ℕ), q < GrT.modes.length → ∀ σ, σ mvT = (q : ℝ) →
      Formula.sat (Formula.and (FM gT gsT) envT) σ →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, GrT.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrT.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gT gsT) envT)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrT] using hq
  have hsingle : ∀ (a : ℕ × RMode (Var 6) × REdge (Var 6)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 6) × REdge (Var 6))
      (b : ℕ × RMode (Var 6) × REdge (Var 6)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 6) × REdge (Var 6)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  simp only [leftProgsT, leftDataT, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  all_goals interval_cases q
  -- window STEEP: every start couples in place
  · exact ⟨[(0, modeT 0, edgeT 0 0)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 0 (by norm_num), edgeT_mem 0 0 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 0 0 (by norm_num) (by norm_num) dt hdt hv00 [] (by simp) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(1, modeT 1, edgeT 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 1 (by norm_num), edgeT_mem 1 1 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 0 1 (by norm_num) (by norm_num) dt hdt hv01 [] (by simp) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(2, modeT 2, edgeT 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 2 (by norm_num), edgeT_mem 2 2 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 0 2 (by norm_num) (by norm_num) dt hdt hv02 [] (by simp) hσ
        simpa [modeT] using this)⟩
  -- window MODER: start STEEP climbs, the rest in place
  · exact ⟨[(0, modeT 0, edgeT 0 1), (1, modeT 1, edgeT 1 1)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrT_modeAt 0 (by norm_num), edgeT_mem 0 1 (by simp [GrT])⟩
        · exact ⟨GrT_modeAt 1 (by norm_num), edgeT_mem 1 1 (by simp [GrT])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 1 1 (by norm_num) (by norm_num) dt hdt hv11 [0]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(1, modeT 1, edgeT 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 1 (by norm_num), edgeT_mem 1 1 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 1 1 (by norm_num) (by norm_num) dt hdt hv11 [] (by simp) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(2, modeT 2, edgeT 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 2 (by norm_num), edgeT_mem 2 2 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 1 2 (by norm_num) (by norm_num) dt hdt hv12 [] (by simp) hσ
        simpa [modeT] using this)⟩
  -- window FLAT: climb to FLAT from behind, in place at FLAT
  · exact ⟨[(0, modeT 0, edgeT 0 1), (1, modeT 1, edgeT 1 2), (2, modeT 2, edgeT 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrT_modeAt 0 (by norm_num), edgeT_mem 0 1 (by simp [GrT])⟩
        · exact ⟨GrT_modeAt 1 (by norm_num), edgeT_mem 1 2 (by simp [GrT])⟩
        · exact ⟨GrT_modeAt 2 (by norm_num), edgeT_mem 2 2 (by simp [GrT])⟩),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 2 2 (by norm_num) (by norm_num) dt hdt hv22 [0, 1]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(1, modeT 1, edgeT 1 2), (2, modeT 2, edgeT 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrT_modeAt 1 (by norm_num), edgeT_mem 1 2 (by simp [GrT])⟩
        · exact ⟨GrT_modeAt 2 (by norm_num), edgeT_mem 2 2 (by simp [GrT])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 2 2 (by norm_num) (by norm_num) dt hdt hv22 [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeT] using this)⟩
  · exact ⟨[(2, modeT 2, edgeT 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrT_modeAt 2 (by norm_num), edgeT_mem 2 2 (by simp [GrT])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondT 2 2 (by norm_num) (by norm_num) dt hdt hv22 [] (by simp) hσ
        simpa [modeT] using this)⟩

/-- **`refinement_ladder_rover_rung1_2to3`, modal Theorem 3** — the first plain
list-invariant instance (multiF chain, climb dispatch, no vacuity). -/
theorem rover_dof_terrain_rung2_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdT 0 0) (hv01 : VerdT 0 1) (hv02 : VerdT 0 2)
    (hv11 : VerdT 1 1) (hv12 : VerdT 1 2) (hv22 : VerdT 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsT dt))
      (rightAutomatonBody GrT mvT)
      (RFormula.and (RFormula.and (canonInvM gT gsT) (envLR domLT domRT))
        (mvValidR mvT GrT.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrT mvT (FM gT gsT) domLT domRT (leftProgsT dt)
    (canonInvM gT gsT) (encode_canonInvM gT gsT) ?_ ?_ ?_
  · exact hdis_multi GrT 0 1 dt leftDataT (by decide) httT hRvT hLT
  · exact hstep_assembled_multiF GrT mvT (FM gT gsT) envT (leftProgsT dt)
      hmvFT hmvenvT hfreshT httT hltT (hframesT dt)
      (HmultiT dt hdt hv00 hv01 hv02 hv11 hv12 hv22)
  · exact hddF_multiE GrT 0 1 dt leftDataT (canonInvM gT gsT) domLT domRT (by decide)
      httT hRvT hLT
      (canonInvM_varsL gT gsT (by
        intro g' hg'
        simp only [gT, gsT, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gT gsT) hdomLT hdomRT


end RoverDofTerrainRung2Modal
end RelCertifier