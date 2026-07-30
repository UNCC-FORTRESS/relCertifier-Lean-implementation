/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `story2_lateral_rung_a_8dof`, modal Theorem 3 (the stratA pilot)

The first AFFINE-FACE (L1c `stratA`) instance: the lateral coordinate rides the
equilibrium face `y ≥ 0` under `y' = −y` — the non-strict Lie route provably
fails off-face, so the face is discharged by `driven_bound_lo_raw` through
`HExistSegB_of_viability_stratA` with the affine datum `(y, λ = 1, M = 0, C = 0)`.
The ball bounds get their lower `y` band from an AUXILIARY strict face `y ≥ −1`
(strict for the decay field at −1, trivially satisfied at anchors) — the
recorded stratified-consumer limitation bypassed without an L1a variant.

Otherwise the plain multiF pattern: seven components in the cover's
stratified-DC order, rung2c's double-bracket position row at the same
coordinate indices, one-way chain, climb dispatch. Existence Z3-free
(`K = 8`, `L = 8`). Residuals: six stratified-DC packs (`VerdY l m`, seven
queries each). Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.AffineFaces
import RelCertifier.Instances.BenchIR.story2_lateral_rung_a_8dof

namespace RelCertifier
namespace Story2LateralAModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 3200000

def vsY : List String := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
def dummyY : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLY (l : ℕ) : Parse.PMode := story2_lateral_rung_a_8dof_IR.L.modes.getD l dummyY
def mRY (q : ℕ) : Parse.PMode := story2_lateral_rung_a_8dof_IR.R.modes.getD q dummyY

abbrev mvY : Var 8 := (Side.Aux, 0)
abbrev aY : Fin 8 := (1 : Fin 8)
abbrev tgY : Var 8 := (Side.Aux, aY)

noncomputable def fLY (l : ℕ) : Fin 8 → Term (Var 8) := hostDyn vsY 8 Side.L (mLY l)
noncomputable def fRY (q : ℕ) : Fin 8 → Term (Var 8) := hostDyn vsY 8 Side.R (mRY q)
noncomputable def domLY : Formula (Var 8) := hostEvolve vsY 8 Side.L (mLY 0)
noncomputable def domRY : Formula (Var 8) := hostEvolve vsY 8 Side.R (mRY 0)
noncomputable def envY : Formula (Var 8) := Formula.and domLY domRY

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invYPF : Parse.PForm :=
  (story2_lateral_rung_a_8dof_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 8) :=
  ((Run.invToG vsY 8 ((atomsOf invYPF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gY : Term (Var 8) := gAt 0
noncomputable def gsY : List (Term (Var 8)) := [gAt 1, gAt 3, gAt 4, gAt 5, gAt 6, gAt 2]
theorem fLY_pipe (l : ℕ) (i : Fin 8) : fLY l i =
    (((some (mLY l)).bind (Run.dynOf vsY 8 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRY_pipe (q : ℕ) (i : Fin 8) : fRY q i =
    (((some (mRY q)).bind (Run.dynOf vsY 8 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLY_pipe : domLY =
    (((some (mLY 0)).bind (fun m => Run.lowerF vsY 8 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRY_pipe : domRY =
    (((some (mRY 0)).bind (fun m => Run.lowerF vsY 8 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLY (l : ℕ) (hl : l < 3) : ∀ i, (fLY l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsY) (some (mLY l))
    (by interval_cases l <;>
      simp [mLY, story2_lateral_rung_a_8dof_IR, Parse.PExpr.namesFree]) i x
    (fLY_pipe l i ▸ hx))

theorem hfRY (q : ℕ) (hq : q < 3) : ∀ i, (fRY q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsY) (some (mRY q))
    (by interval_cases q <;>
      simp [mRY, story2_lateral_rung_a_8dof_IR, Parse.PExpr.namesFree]) i x
    (fRY_pipe q i ▸ hx))

theorem hdomLY : domLY.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsY) (some (mLY 0))
    (by simp [mLY, story2_lateral_rung_a_8dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLY_pipe ▸ hx))

theorem hdomRY : domRY.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsY) (some (mRY 0))
    (by simp [mRY, story2_lateral_rung_a_8dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRY_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gY :: gsY, mvY ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gY, gsY, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gY :: gsY, tgY ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gY, gsY, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFY : mvY ∉ (FM gY gsY).fv := notMem_FM_fv hmvg
theorem htgFY : tgY ∉ (FM gY gsY).fv := notMem_FM_fv htgg

theorem hmvenvY : mvY ∉ envY.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLY h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRY h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvY : tgY ∉ envY.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLY h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRY h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph -/

noncomputable def modeY (q : ℕ) : RMode (Var 8) :=
  { sys := rightBlock (fRY q) (Term.const 1), dom := domRY, weight := 1 }

def edgeY (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrY : SearchGraph (Var 8) :=
  { modes := [modeY 0, modeY 1, modeY 2],
    edges := [edgeY 0 1, edgeY 0 0, edgeY 1 2, edgeY 1 1, edgeY 2 2] }

theorem GrY_modeAt (q : ℕ) (hq : q < 3) : GrY.modeAt q = some (modeY q) := by
  interval_cases q <;> rfl

theorem httY : ∀ q, ∀ e ∈ GrY.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrY.edges := List.mem_of_mem_filter he
  simp only [GrY, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltY : ∀ q, ∀ e ∈ GrY.edgesFrom q, e.tgt < GrY.modes.length := by
  intro q e he
  have hmem : e ∈ GrY.edges := List.mem_of_mem_filter he
  simp only [GrY, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrY, edgeY]

theorem hRvY : ∀ q m, GrY.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeY q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrY] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrY] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrY] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrY])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRY q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRY q) (Term.const 1) (hfRY q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRY hy

theorem edgeY_mem : ∀ st tgt, edgeY st tgt ∈ GrY.edges →
    edgeY st tgt ∈ GrY.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeY]⟩

theorem hfreshY : ∀ q m, GrY.modeAt q = some m →
    mvY ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvY q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataY : List ((Fin 8 → Term (Var 8)) × Formula (Var 8) × ℕ) :=
  [(fLY 0, domLY, 1), (fLY 1, domLY, 1), (fLY 2, domLY, 1)]

noncomputable def leftProgsY (dt : ℝ) : List (Program (Var 8)) :=
  leftDataY.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgY dt d.2.2)

theorem hLY : ∀ d ∈ leftDataY, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataY, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLY 0 (by norm_num), hdomLY⟩
  · exact ⟨hfLY 1 (by norm_num), hdomLY⟩
  · exact ⟨hfLY 2 (by norm_num), hdomLY⟩

theorem hframesY (dt : ℝ) : ∀ P ∈ leftProgsY dt, FramesMv P mvY := by
  intro P hP
  simp only [leftProgsY, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgY dt d.2.2 mvY (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi


/-! ## Parse pins -/

theorem hy030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hym1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hym10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hy0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hy00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hy1 : Run.parseRat "1" = some 1 := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hy05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hy08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hym05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hy06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstY (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRY0_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 0) x = 3 * (cstY q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstY]
theorem fRY1_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY2_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY3_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY4_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY5_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 5) x = -1 * x (Rv 5) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY6_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 6) x = 0 := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fRY7_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRY q 7) x = -1 * x (Rv 7) := by
  interval_cases q <;>
    simp [fRY, hostDyn, mRY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, hy3, hy030, hy050, hy065, hym1, hym10, hy0, hy1, hy05, hy03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem sat_domRY (x : State (Var 8)) : Formula.sat domRY x ↔
    (-(1:ℝ)/2 ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/20 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/20 ∧ 0 ≤ x (Rv 4) ∧
     x (Rv 4) ≤ 3/20 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/20) := by
  simp only [domRY, hostEvolve, mRY, story2_lateral_rung_a_8dof_IR, vsY]
  simp [Run.lowerF, Run.lowerE, hym05, hy06, hy015, hy00, hy08, hym10,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

/-! ## Faces: 12 strict (incl. the auxiliary `y ≥ −1` band face), the conditioned
`s` face, and the affine equilibrium face `y ≥ 0` (the stratA datum) -/

noncomputable def faceVLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))
noncomputable def facePsiLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 2))
noncomputable def facePsiHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 2)) (Term.const ((3:ℝ)/20))
noncomputable def faceThLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 3))
noncomputable def faceThHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 3)) (Term.const ((3:ℝ)/20))
noncomputable def faceYHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 4)) (Term.const ((3:ℝ)/20))
noncomputable def faceYAux : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 4))
noncomputable def faceZLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 5))
noncomputable def faceZHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 5)) (Term.const ((3:ℝ)/20))
noncomputable def faceWLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 7))
noncomputable def faceWHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 7)) (Term.const ((3:ℝ)/20))
noncomputable def faceSLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))
noncomputable def facePhLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 6))
noncomputable def facePhHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 6)) (Term.const ((3:ℝ)/5))

noncomputable def gsSY : List (Term (Var 8)) :=
  [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi,
   faceYHi, faceYAux, faceZLo, faceZHi, faceWLo, faceWHi]
noncomputable def gsNY : List (Term (Var 8)) := [faceSLo, facePhLo, facePhHi]
noncomputable def gsALY : List (Var 8 × ℝ × ℝ × ℝ) := [((Rv 4 : Var 8), 1, 0, 0)]

theorem faces_fv_RY : ∀ gT' ∈ gsSY ++ gsNY, ∀ x ∈ gT'.fv, x ∈ range Rv := by
  intro gT' hgT x hx
  simp only [gsSY, gsNY, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi,
        faceYHi, faceYAux, faceZLo, faceZHi, faceWLo, faceWHi, faceSLo, facePhLo,
        facePhHi, Term.fv,
        Set.mem_union, Set.mem_empty_iff_false, false_or, or_false,
        Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

theorem odeField_RY (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    odeField (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cstY q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0) *
          ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))
        else if c = Rv 2 then -1 * x (Rv 2)
        else if c = Rv 3 then -1 * x (Rv 3)
        else if c = Rv 4 then -1 * x (Rv 4)
        else if c = Rv 5 then -1 * x (Rv 5)
        else if c = Rv 7 then -1 * x (Rv 7)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
      intro a b hab
      simp [Rv, Prod.ext_iff]
      exact fun h => hab (by exact_mod_cast h)
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have hLR : ∀ k : Fin 8, (Lv j : Var 8) ≠ Rv k := by
        intro k
        simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, hLR 0, hLR 1, hLR 2, hLR 3, hLR 4, hLR 5, hLR 7]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRY0_eval q hq]
      · simp [Term.eval, AOp.interp, fRY1_eval q hq,
          hne 1 0 (by decide)]
      · simp [Term.eval, AOp.interp, fRY2_eval q hq,
          hne 2 0 (by decide),
          hne 2 1 (by decide)]
      · simp [Term.eval, AOp.interp, fRY3_eval q hq,
          hne 3 0 (by decide),
          hne 3 1 (by decide),
          hne 3 2 (by decide)]
      · simp [Term.eval, AOp.interp, fRY4_eval q hq,
          hne 4 0 (by decide),
          hne 4 1 (by decide),
          hne 4 2 (by decide),
          hne 4 3 (by decide)]
      · simp [Term.eval, AOp.interp, fRY5_eval q hq,
          hne 5 0 (by decide),
          hne 5 1 (by decide),
          hne 5 2 (by decide),
          hne 5 3 (by decide),
          hne 5 4 (by decide)]
      · simp [Term.eval, AOp.interp, fRY6_eval q hq,
          hne 6 0 (by decide),
          hne 6 1 (by decide),
          hne 6 2 (by decide),
          hne 6 3 (by decide),
          hne 6 4 (by decide),
          hne 6 5 (by decide),
          hne 6 7 (by decide)]
      · simp [Term.eval, AOp.interp, fRY7_eval q hq,
          hne 7 0 (by decide),
          hne 7 1 (by decide),
          hne 7 2 (by decide),
          hne 7 3 (by decide),
          hne 7 4 (by decide),
          hne 7 5 (by decide)]
  · have hnotR : ∀ j : Fin 8, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1), if_neg (hnotR 2), if_neg (hnotR 3), if_neg (hnotR 4), if_neg (hnotR 5), if_neg (hnotR 7)]

theorem hbndS_Y (q : ℕ) (hq : q < 3) : ∀ gT' ∈ gsSY, ∀ x : State (Var 8),
    Term.eval gT' x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1))
      (fun ω => Term.eval gT' ω) x < 0 := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro gT' hgT x hface
  simp only [gsSY, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hx : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + (0) := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) (0) x,
      odeField_RY q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx]
    interval_cases q <;> norm_num [cstY]
  · have hx : x (Rv 0) = (4:ℝ)/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-((4:ℝ)/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-((4:ℝ)/5)) x,
      odeField_RY q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx]
    interval_cases q <;> norm_num [cstY]
  · have hx : x (Rv 2) = -(1:ℝ)/2 := by
      simp only [facePsiLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePsiLo ω)
        = fun y => (-1 : ℝ) * y (Rv 2) + (-(1:ℝ)/2) := by
      funext y; simp [facePsiLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) (-1) (-(1:ℝ)/2) x,
      odeField_RY q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 2) = (3:ℝ)/20 := by
      simp only [facePsiHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePsiHi ω)
        = fun y => (1 : ℝ) * y (Rv 2) + (-((3:ℝ)/20)) := by
      funext y; simp [facePsiHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) 1 (-((3:ℝ)/20)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 3) = -(1:ℝ)/2 := by
      simp only [faceThLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 3) + (-(1:ℝ)/2) := by
      funext y; simp [faceThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) (-1) (-(1:ℝ)/2) x,
      odeField_RY q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)), if_neg (hne 3 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 3) = (3:ℝ)/20 := by
      simp only [faceThHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceThHi ω)
        = fun y => (1 : ℝ) * y (Rv 3) + (-((3:ℝ)/20)) := by
      funext y; simp [faceThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) 1 (-((3:ℝ)/20)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)), if_neg (hne 3 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = (3:ℝ)/20 := by
      simp only [faceYHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceYHi ω)
        = fun y => (1 : ℝ) * y (Rv 4) + (-((3:ℝ)/20)) := by
      funext y; simp [faceYHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) 1 (-((3:ℝ)/20)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), if_neg (hne 4 3 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = -(1:ℝ) := by
      simp only [faceYAux, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceYAux ω)
        = fun y => (-1 : ℝ) * y (Rv 4) + (-(1:ℝ)) := by
      funext y; simp [faceYAux, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) (-1) (-(1:ℝ)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), if_neg (hne 4 3 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 5) = -(1:ℝ) := by
      simp only [faceZLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceZLo ω)
        = fun y => (-1 : ℝ) * y (Rv 5) + (-(1:ℝ)) := by
      funext y; simp [faceZLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) (-1) (-(1:ℝ)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)), if_neg (hne 5 2 (by decide)), if_neg (hne 5 3 (by decide)), if_neg (hne 5 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 5) = (3:ℝ)/20 := by
      simp only [faceZHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceZHi ω)
        = fun y => (1 : ℝ) * y (Rv 5) + (-((3:ℝ)/20)) := by
      funext y; simp [faceZHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) 1 (-((3:ℝ)/20)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)), if_neg (hne 5 2 (by decide)), if_neg (hne 5 3 (by decide)), if_neg (hne 5 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 7) = -(1:ℝ) := by
      simp only [faceWLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceWLo ω)
        = fun y => (-1 : ℝ) * y (Rv 7) + (-(1:ℝ)) := by
      funext y; simp [faceWLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) (-1) (-(1:ℝ)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)), if_neg (hne 7 2 (by decide)), if_neg (hne 7 3 (by decide)), if_neg (hne 7 4 (by decide)), if_neg (hne 7 5 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 7) = (3:ℝ)/20 := by
      simp only [faceWHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceWHi ω)
        = fun y => (1 : ℝ) * y (Rv 7) + (-((3:ℝ)/20)) := by
      funext y; simp [faceWHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) 1 (-((3:ℝ)/20)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)), if_neg (hne 7 2 (by decide)), if_neg (hne 7 3 (by decide)), if_neg (hne 7 4 (by decide)), if_neg (hne 7 5 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num

theorem hbndN_Y (q : ℕ) (hq : q < 3) : ∀ i (hi : i < gsNY.length), ∀ x : State (Var 8),
    (∀ gT' ∈ gsSY ++ ([] : List (Term (Var 8))), Term.eval gT' x ≤ 0) →
    Lie (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1))
      (fun ω => Term.eval gsNY[i] ω) x ≤ 0 := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro i hi x hx
  have hi3 : i < 3 := by simpa [gsNY] using hi
  interval_cases i
  case «1» =>
    show Lie _ (fun ω => Term.eval facePhLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval facePhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 6) + (-(1/2)) := by
      funext y; simp [facePhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) (-1) (-(1/2)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 3 (by decide)),
      if_neg (hne 6 4 (by decide)), if_neg (hne 6 5 (by decide)),
      if_neg (hne 6 7 (by decide))]
    norm_num
  case «2» =>
    show Lie _ (fun ω => Term.eval facePhHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval facePhHi ω)
        = fun y => (1 : ℝ) * y (Rv 6) + (-(3/5)) := by
      funext y; simp [facePhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) 1 (-(3/5)) x,
      odeField_RY q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 3 (by decide)),
      if_neg (hne 6 4 (by decide)), if_neg (hne 6 5 (by decide)),
      if_neg (hne 6 7 (by decide))]
    norm_num
  case «0» =>
  have hv0 : 0 ≤ x (Rv 0) := by
    have := hx faceVLo (List.mem_append_left _ (by simp [gsSY]))
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
    have := hx facePsiLo (List.mem_append_left _ (by simp [gsSY]))
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hp2 : x (Rv 2) ≤ 3/20 := by
    have := hx facePsiHi (List.mem_append_left _ (by simp [gsSY]))
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have ht1 : -(1:ℝ)/2 ≤ x (Rv 3) := by
    have := hx faceThLo (List.mem_append_left _ (by simp [gsSY]))
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have ht2 : x (Rv 3) ≤ 3/20 := by
    have := hx faceThHi (List.mem_append_left _ (by simp [gsSY]))
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  show Lie _ (fun ω => Term.eval faceSLo ω) x ≤ 0
  have hfun : (fun ω : State (Var 8) => Term.eval faceSLo ω)
      = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
    funext y; simp [faceSLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
    odeField_RY q hq]
  simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
  have hB : (0:ℝ) ≤ (1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)) := by
    nlinarith [sq_nonneg (x (Rv 2)), sq_nonneg (x (Rv 3))]
  have := mul_nonneg hv0 hB
  linarith
/-! ## Lipschitz (rung2c double-bracket core + decay rows) -/

theorem hLip_Y (q : ℕ) (hq : q < 3) (ν : State (Var 8))
    (hν : ∀ gT ∈ gsSY, Term.eval gT ν ≤ 0) :
    LipschitzOnWith 8 (odeField (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  have hν0lo : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsSY])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν0hi : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsSY])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hν2lo : -(1:ℝ)/2 ≤ ν (Rv 2) := by
    have := hν facePsiLo (by simp [gsSY])
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hν2hi : ν (Rv 2) ≤ 3/20 := by
    have := hν facePsiHi (by simp [gsSY])
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have hν3lo : -(1:ℝ)/2 ≤ ν (Rv 3) := by
    have := hν faceThLo (by simp [gsSY])
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have hν3hi : ν (Rv 3) ≤ 3/20 := by
    have := hν faceThHi (by simp [gsSY])
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RY q hq, odeField_RY q hq]
  rw [Metric.mem_closedBall] at hx hy
  have hcb : ∀ (w : State (Var 8)), dist w ν ≤ 1 → ∀ j : Fin 8,
      |w (Rv j) - ν (Rv j)| ≤ 1 := by
    intro w hw j
    have h := dist_le_pi_dist w ν (Rv j)
    rw [Real.dist_eq] at h
    linarith
  have hx0 : |x (Rv 0)| ≤ 9/5 := by
    have h := hcb x hx 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν0hi⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hy0 : |y (Rv 0)| ≤ 9/5 := by
    have h := hcb y hy 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν0hi⟩
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hx2 : |x (Rv 2)| ≤ 3/2 := by
    have h := hcb x hx 2
    have hνb : |ν (Rv 2)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 2)) (ν (Rv 2))
    linarith [abs_le.mp hνb]
  have hy2 : |y (Rv 2)| ≤ 3/2 := by
    have h := hcb y hy 2
    have hνb : |ν (Rv 2)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 2)) (ν (Rv 2))
    linarith [abs_le.mp hνb]
  have hx3 : |x (Rv 3)| ≤ 3/2 := by
    have h := hcb x hx 3
    have hνb : |ν (Rv 3)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 3)) (ν (Rv 3))
    linarith [abs_le.mp hνb]
  have hy3 : |y (Rv 3)| ≤ 3/2 := by
    have h := hcb y hy 3
    have hνb : |ν (Rv 3)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 3)) (ν (Rv 3))
    linarith [abs_le.mp hνb]
  have hdc : ∀ j : Fin 8, |x (Rv j) - y (Rv j)| ≤ dist x y := by
    intro j
    have h := dist_le_pi_dist x y (Rv j)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  have hcoe : ((8 : NNReal) : ℝ) = 8 := rfl
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : 3 * (cstY q - x (Rv 0)) - 3 * (cstY q - y (Rv 0))
        = -3 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have h0 := hdc 0
    have habs : |(-3 : ℝ)| = 3 := by norm_num
    rw [habs, hcoe]
    nlinarith
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h10, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2)))
          - 3/10 * (x (Rv 3) * x (Rv 3)))
        - y (Rv 0) * ((1 - 1/2 * (y (Rv 2) * y (Rv 2)))
          - 3/10 * (y (Rv 3) * y (Rv 3)))
        = ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))
            * (x (Rv 0) - y (Rv 0))
          + y (Rv 0) * (-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
              - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3)))) := by
      ring
    rw [hdiff]
    have hBx : |(1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))|
        ≤ 14/5 := by
      have h2 : x (Rv 2) * x (Rv 2) ≤ 9/4 := by nlinarith [abs_le.mp hx2]
      have h3 : x (Rv 3) * x (Rv 3) ≤ 9/4 := by nlinarith [abs_le.mp hx3]
      have h2n : 0 ≤ x (Rv 2) * x (Rv 2) := mul_self_nonneg _
      have h3n : 0 ≤ x (Rv 3) * x (Rv 3) := mul_self_nonneg _
      rw [abs_le]
      constructor <;> nlinarith
    have hsum2 : |x (Rv 2) + y (Rv 2)| ≤ 3 := by
      calc |x (Rv 2) + y (Rv 2)| ≤ |x (Rv 2)| + |y (Rv 2)| := abs_add_le _ _
        _ ≤ 3 := by linarith
    have hsum3 : |x (Rv 3) + y (Rv 3)| ≤ 3 := by
      calc |x (Rv 3) + y (Rv 3)| ≤ |x (Rv 3)| + |y (Rv 3)| := abs_add_le _ _
        _ ≤ 3 := by linarith
    have hrest : |(-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
          - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))))|
        ≤ 12/5 * dist x y := by
      have hA : |(x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2))| ≤ 3 * dist x y := by
        rw [abs_mul]
        have := hdc 2
        nlinarith [abs_nonneg (x (Rv 2) + y (Rv 2)), abs_nonneg (x (Rv 2) - y (Rv 2))]
      have hB : |(x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))| ≤ 3 * dist x y := by
        rw [abs_mul]
        have := hdc 3
        nlinarith [abs_nonneg (x (Rv 3) + y (Rv 3)), abs_nonneg (x (Rv 3) - y (Rv 3))]
      have htri : |(-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
            - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))))|
          ≤ |(-(1/2)) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))|
            + |(3/10) * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3)))| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
      have e1 : |(-(1/2) : ℝ) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))|
          ≤ 1/2 * (3 * dist x y) := by
        rw [abs_mul]
        have h : |(-(1/2) : ℝ)| = 1/2 := by norm_num
        rw [h]
        nlinarith [abs_nonneg ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))]
      have e2 : |((3:ℝ)/10) * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3)))|
          ≤ 3/10 * (3 * dist x y) := by
        rw [abs_mul]
        have h : |((3:ℝ)/10)| = 3/10 := by norm_num
        rw [h]
        nlinarith [abs_nonneg ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3)))]
      linarith
    calc |((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))
            * (x (Rv 0) - y (Rv 0))
          + y (Rv 0) * (-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
              - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))))|
        ≤ |((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))
            * (x (Rv 0) - y (Rv 0))|
          + |y (Rv 0) * (-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
              - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))))| :=
          abs_add_le _ _
      _ ≤ ((8 : NNReal) : ℝ) * dist x y := by
          rw [abs_mul, abs_mul, hcoe]
          have h0 := hdc 0
          nlinarith [abs_nonneg (x (Rv 0) - y (Rv 0)),
            abs_nonneg (y (Rv 0)),
            abs_nonneg ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))),
            abs_nonneg (-(1/2) * ((x (Rv 2) + y (Rv 2)) * (x (Rv 2) - y (Rv 2)))
              - 3/10 * ((x (Rv 3) + y (Rv 3)) * (x (Rv 3) - y (Rv 3))))]
  by_cases hc2 : c = Rv 2
  · subst hc2
    have h20 : (Rv (2 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 2) - -1 * y (Rv 2) = -(x (Rv 2) - y (Rv 2)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 2
    nlinarith
  by_cases hc3 : c = Rv 3
  · subst hc3
    have h30 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h31 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h32 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 3) - -1 * y (Rv 3) = -(x (Rv 3) - y (Rv 3)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 3
    nlinarith
  by_cases hc4 : c = Rv 4
  · subst hc4
    have h40 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h41 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h42 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h43 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h40, if_neg h41, if_neg h42, if_neg h43,
      eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 4) - -1 * y (Rv 4) = -(x (Rv 4) - y (Rv 4)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 4
    nlinarith
  by_cases hc5 : c = Rv 5
  · subst hc5
    have h50 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h51 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h52 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h53 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    have h54 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 4 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h50, if_neg h51, if_neg h52, if_neg h53, if_neg h54,
      eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 5) - -1 * y (Rv 5) = -(x (Rv 5) - y (Rv 5)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 5
    nlinarith
  by_cases hc7 : c = Rv 7
  · subst hc7
    have h70 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h71 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h72 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h73 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    have h74 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 4 := by simp [Rv, Prod.ext_iff]
    have h75 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 5 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h70, if_neg h71, if_neg h72, if_neg h73, if_neg h74,
      if_neg h75, eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 7) - -1 * y (Rv 7) = -(x (Rv 7) - y (Rv 7)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 7
    nlinarith
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4,
      if_neg hc5, if_neg hc7]
    simp [dist_nonneg]

/-! ## Field bound -/

theorem hfbnd_Y (q : ℕ) (hq : q < 3) (ν : State (Var 8))
    (hν : ∀ gT ∈ gsSY, Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRY q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  intro x hx
  have hν0lo : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsSY])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν0hi : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsSY])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hν2lo : -(1:ℝ)/2 ≤ ν (Rv 2) := by
    have := hν facePsiLo (by simp [gsSY])
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hν2hi : ν (Rv 2) ≤ 3/20 := by
    have := hν facePsiHi (by simp [gsSY])
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have hν3lo : -(1:ℝ)/2 ≤ ν (Rv 3) := by
    have := hν faceThLo (by simp [gsSY])
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have hν3hi : ν (Rv 3) ≤ 3/20 := by
    have := hν faceThHi (by simp [gsSY])
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  rw [Metric.mem_closedBall] at hx
  have hcb : ∀ j : Fin 8, |x (Rv j) - ν (Rv j)| ≤ 1 := by
    intro j
    have h := dist_le_pi_dist x ν (Rv j)
    rw [Real.dist_eq] at h
    linarith
  have hx0 : |x (Rv 0)| ≤ 9/5 := by
    have h := hcb 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν0hi⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hx2 : |x (Rv 2)| ≤ 3/2 := by
    have h := hcb 2
    have hνb : |ν (Rv 2)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 2)) (ν (Rv 2))
    linarith [abs_le.mp hνb]
  have hx3 : |x (Rv 3)| ≤ 3/2 := by
    have h := hcb 3
    have hνb : |ν (Rv 3)| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 3)) (ν (Rv 3))
    linarith [abs_le.mp hνb]
  rw [odeField_RY q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cstY q ∧ cstY q ≤ 13/20 := by
      interval_cases q <;> norm_num [cstY]
    rw [abs_le]
    push_cast
    obtain ⟨hc1, hc2⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hx0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h10, if_pos rfl, Real.norm_eq_abs]
    have hBx : |(1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))|
        ≤ 14/5 := by
      have h2 : x (Rv 2) * x (Rv 2) ≤ 9/4 := by nlinarith [abs_le.mp hx2]
      have h3 : x (Rv 3) * x (Rv 3) ≤ 9/4 := by nlinarith [abs_le.mp hx3]
      have h2n : 0 ≤ x (Rv 2) * x (Rv 2) := mul_self_nonneg _
      have h3n : 0 ≤ x (Rv 3) * x (Rv 3) := mul_self_nonneg _
      rw [abs_le]
      constructor <;> nlinarith
    rw [abs_mul]
    push_cast
    nlinarith [abs_nonneg (x (Rv 0)),
      abs_nonneg ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))]
  by_cases hc2 : c = Rv 2
  · subst hc2
    have h20 : (Rv (2 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, Real.norm_eq_abs]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hx2, abs_nonneg (x (Rv 2))]
  by_cases hc3 : c = Rv 3
  · subst hc3
    have h30 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h31 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h32 : (Rv (3 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl, Real.norm_eq_abs]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hx3, abs_nonneg (x (Rv 3))]
  by_cases hc4 : c = Rv 4
  · subst hc4
    have h40 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h41 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h42 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h43 : (Rv (4 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h40, if_neg h41, if_neg h42, if_neg h43,
      eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hy1 : -(1:ℝ) ≤ ν (Rv 4) := by
      have := hν faceYAux (by simp [gsSY])
      simp only [faceYAux, Term.eval, AOp.interp] at this; linarith
    have hy2 : ν (Rv 4) ≤ 3/20 := by
      have := hν faceYHi (by simp [gsSY])
      simp only [faceYHi, Term.eval, AOp.interp] at this; linarith
    have hxb : |x (Rv 4)| ≤ 2 := by
      have h := dist_le_pi_dist x ν (Rv 4)
      rw [Real.dist_eq] at h
      have hνb : |ν (Rv 4)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 := abs_sub_abs_le_abs_sub (x (Rv 4)) (ν (Rv 4))
      have h3 : |x (Rv 4) - ν (Rv 4)| ≤ 1 := by linarith [hx]
      linarith [abs_le.mp hνb]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hxb, abs_nonneg (x (Rv 4))]
  by_cases hc5 : c = Rv 5
  · subst hc5
    have h50 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h51 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h52 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h53 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    have h54 : (Rv (5 : Fin 8) : Var 8) ≠ Rv 4 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h50, if_neg h51, if_neg h52, if_neg h53, if_neg h54,
      eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hz1 : -(1:ℝ) ≤ ν (Rv 5) := by
      have := hν faceZLo (by simp [gsSY])
      simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
    have hz2 : ν (Rv 5) ≤ 3/20 := by
      have := hν faceZHi (by simp [gsSY])
      simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
    have hxb : |x (Rv 5)| ≤ 2 := by
      have h := dist_le_pi_dist x ν (Rv 5)
      rw [Real.dist_eq] at h
      have hνb : |ν (Rv 5)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 := abs_sub_abs_le_abs_sub (x (Rv 5)) (ν (Rv 5))
      have h3 : |x (Rv 5) - ν (Rv 5)| ≤ 1 := by linarith [hx]
      linarith [abs_le.mp hνb]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hxb, abs_nonneg (x (Rv 5))]
  by_cases hc7 : c = Rv 7
  · subst hc7
    have h70 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h71 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h72 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    have h73 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
    have h74 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 4 := by simp [Rv, Prod.ext_iff]
    have h75 : (Rv (7 : Fin 8) : Var 8) ≠ Rv 5 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h70, if_neg h71, if_neg h72, if_neg h73, if_neg h74,
      if_neg h75, eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hw1 : -(1:ℝ) ≤ ν (Rv 7) := by
      have := hν faceWLo (by simp [gsSY])
      simp only [faceWLo, Term.eval, AOp.interp] at this; linarith
    have hw2 : ν (Rv 7) ≤ 3/20 := by
      have := hν faceWHi (by simp [gsSY])
      simp only [faceWHi, Term.eval, AOp.interp] at this; linarith
    have hxb : |x (Rv 7)| ≤ 2 := by
      have h := dist_le_pi_dist x ν (Rv 7)
      rw [Real.dist_eq] at h
      have hνb : |ν (Rv 7)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 := abs_sub_abs_le_abs_sub (x (Rv 7)) (ν (Rv 7))
      have h3 : |x (Rv 7) - ν (Rv 7)| ≤ 1 := by linarith [hx]
      linarith [abs_le.mp hνb]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hxb, abs_nonneg (x (Rv 7))]
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4,
      if_neg hc5, if_neg hc7]
    norm_num


/-! ## Existence — the first stratA discharge (affine equilibrium face) -/

theorem esY (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM gY gsY) envY) σ →
      HExistSegB (fLY l) (fRY m) (Term.const 1) domLY domRY dt
        (Function.update σ tgY 0) := by
  intro σ hσ
  have hR : Formula.sat domRY σ := hσ.2.2
  rw [sat_domRY] at hR
  obtain ⟨h6l, h6h, h2l, h2h, h1l, h3l, h3h, h0l, h0h, h7l, h7h, h4l, h4h, h5l, h5h⟩ := hR
  have hupd : ∀ j : Fin 8, σ (Side.R, j) = Function.update σ tgY 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgY, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsSY, Term.eval gT' (Function.update σ tgY 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsSY, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYAux, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceWLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceWHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNY, Term.eval gT' (Function.update σ tgY 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNY, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl
    · simp only [faceSLo, Term.eval, AOp.interp, Rv]
      rw [← hupd]; linarith
    · simp only [facePhLo, Term.eval, AOp.interp, Rv]
      rw [← hupd]; linarith
    · simp only [facePhHi, Term.eval, AOp.interp, Rv]
      rw [← hupd]; linarith
  refine HExistSegB_of_viability_stratA (fLY l) (fRY m) (Term.const 1)
    domLY domRY gsSY [] gsNY 0 le_rfl ([] : List (Var 8 × ℝ × ℝ × ℝ)) gsALY
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLY l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RY gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLY l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RY gT' (List.mem_append_right _ hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (by
      intro p hp hb
      simp only [gsALY, List.mem_singleton] at hp
      subst hp
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLY l) _ hb
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (by
      intro p hp
      simp only [gsALY, List.mem_singleton] at hp
      subst hp
      norm_num)
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (by
      intro p hp
      simp only [gsALY, List.mem_singleton] at hp
      subst hp
      norm_num)
    (by
      intro gT' hgT x _ hface
      exact hbndS_Y m hm gT' hgT x hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      exact hbndN_Y m hm i hi x hx)
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (by
      intro p hp x _ _
      simp only [gsALY, List.mem_singleton] at hp
      subst hp
      rw [odeField_RY m hm]
      have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
        if_neg (hne 4 2 (by decide)), if_neg (hne 4 3 (by decide)),
        eq_self_iff_true, if_true, if_pos rfl]
      norm_num)
    (by
      intro x hS hN hAU hAL
      have hS' : ∀ gT' ∈ gsSY, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hv0 : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsSY])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hv8 : x (Rv 0) ≤ 4/5 := by
        have := hS' faceVHi (by simp [gsSY])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsSY])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hp2 : x (Rv 2) ≤ 3/20 := by
        have := hS' facePsiHi (by simp [gsSY])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have hth1 : -(1:ℝ)/2 ≤ x (Rv 3) := by
        have := hS' faceThLo (by simp [gsSY])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have hth2 : x (Rv 3) ≤ 3/20 := by
        have := hS' faceThHi (by simp [gsSY])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hy2 : x (Rv 4) ≤ 3/20 := by
        have := hS' faceYHi (by simp [gsSY])
        simp only [faceYHi, Term.eval, AOp.interp] at this; linarith
      have hz1 : -(1:ℝ) ≤ x (Rv 5) := by
        have := hS' faceZLo (by simp [gsSY])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hz2 : x (Rv 5) ≤ 3/20 := by
        have := hS' faceZHi (by simp [gsSY])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hw1 : -(1:ℝ) ≤ x (Rv 7) := by
        have := hS' faceWLo (by simp [gsSY])
        simp only [faceWLo, Term.eval, AOp.interp] at this; linarith
      have hw2 : x (Rv 7) ≤ 3/20 := by
        have := hS' faceWHi (by simp [gsSY])
        simp only [faceWHi, Term.eval, AOp.interp] at this; linarith
      have hs0 : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNY])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hy0 : 0 ≤ x (Rv 4) := by
        have := hAL ((Rv 4 : Var 8), 1, 0, 0) (by simp [gsALY])
        simpa using this
      have hph1 : -(1:ℝ)/2 ≤ x (Rv 6) := by
        have := hN facePhLo (by simp [gsNY])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hph2 : x (Rv 6) ≤ 3/5 := by
        have := hN facePhHi (by simp [gsNY])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      exact (sat_domRY x).mpr ⟨hph1, hph2, hp1, hp2, hs0, hth1, hth2, hv0, hv8,
        hw1, hw2, hy0, hy2, hz1, hz2⟩)
    8 8 1 one_pos
    (fun ν0 h0 => hLip_Y m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    (fun ν0 h0 => hfbnd_Y m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgY 0)
    hfS
    hfN
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (by
      intro p hp
      simp only [gsALY, List.mem_singleton] at hp
      subst hp
      show (0:ℝ) ≤ Function.update σ tgY 0 (Rv 4)
      rw [← hupd 4]
      exact h4l)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The route verdicts (stratified-DC over the two components) -/

def VerdY (l m : ℕ) : Prop :=
  ∀ i (hi : i < (gY :: gsY).length),
    z3solve (flowQuery ⟨(gY :: gsY)[i], fLY l, fRY m, Term.const 1,
      strataDomHost (Formula.and domLY domRY) ((gY :: gsY).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gY :: gsY)[i], fLY l, fRY m, Term.const 1,
      strataDomHost (Formula.and domLY domRY) ((gY :: gsY).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gY :: gsY)[i], fLY l, fRY m, Term.const 1,
      strataDomHost (Formula.and domLY domRY) ((gY :: gsY).take i)⟩) = Verdict.unsat

/-! ## The certified couplings -/

theorem coupleY (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdY l m) :
    ∀ σ', Formula.sat (Formula.and (FM gY gsY) envY) σ' → σ' tgY = 0 →
      faModalB (Equiv.refl (Var 8))
        (Program.ode (DLCalTiming.clk tgY (leftBlock (fLY l))) domLY)
        (Program.ode (rightBlock (fRY m) (Term.const 1)) domRY)
        (Formula.and (FM gY gsY) envY) tgY dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgY (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgY
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLY l) (fRY m) (Term.const 1)
    (Formula.and domLY domRY) (gY :: gsY) hv
  have hboxes : ∀ g' ∈ gY :: gsY, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLY l) ++ rightBlock (fRY m) (Term.const 1))
      (Formula.and domLY domRY)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gY gsY σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gY gsY (fLY l) (fRY m)
    (Term.const 1) domLY domRY tgY dt
    (LR_blocks_disjoint _ _ _ (hfLY l hl) (hfRY m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLY hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRY hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLY l) _ h
      exact aux_ne_Lv aY i hi)
    (fun h => aux_notin_range_Lv aY (leftBlock_readVars_sub (fLY l) (hfLY l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRY m) (Term.const 1) _ h
      exact aux_ne_Rv aY i hi)
    (fun h => aux_notin_range_Rv aY (rightBlock_readVars_sub (fRY m) (Term.const 1)
      (hfRY m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aY (rightBlock_boundSet_sub (fRY m) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aY (hdomLY h))
    (fun h => aux_notin_range_Rv aY (hdomRY h))
    htgg hboxes
    (esY l m hl hm dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLY ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRY μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLY μ := by
    rwa [(Formula.coincidence domLY (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLY hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRY m) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLY μ ↔ Formula.sat domLY ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Static hops and the window response -/

theorem static_hopY (fR : Fin 8 → Term (Var 8)) (lam : Term (Var 8))
    (φ : Formula (Var 8)) (σ : State (Var 8)) (hσφ : Formula.sat φ σ)
    (hdom : Formula.sat (Formula.and domLY domRY) σ) :
    ∃ ρ, Program.sem ((⟨fR, lam, domRY⟩ : RepoHop 8).prog domLY) σ ρ
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

theorem hops_convY : ∀ (ps : List ℕ), (∀ p ∈ ps, p < 3) →
    List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ → Program.sem q ν μ)
      (ps.map (fun p => (⟨fRY p, Term.const 1, domRY⟩ : RepoHop 8).prog domLY))
      (ps.map (fun p => Program.ode (rightBlock (fRY p) (Term.const 1)) domRY)) := by
  intro ps
  induction ps with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hps
      refine List.Forall₂.cons ?_ (ih (fun p hp => hps p (List.mem_cons_of_mem a hp)))
      intro ν μ hrun
      exact joint_run_toR (hfRY a (hps a List.mem_cons_self)) (by simp [Term.fv]) hrun

/-- The window response: static hops up the chain, the certified coupling at the
reached mode. -/
theorem respondY (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdY l m) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 8)} (hσ : Formula.sat (Formula.and (FM gY gsY) envY) σ) :
    Formula.sat (faModal (Equiv.refl (Var 8))
      (windowSeg (leftBlock (fLY l)) domLY tgY dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRY p) (Term.const 1))
          domRY))
        ++ [Program.ode (rightBlock (fRY m) (Term.const 1)) domRY]))
      (Formula.and (FM gY gsY) envY)) σ := by
  have hfa := Hmulti_window1_prefixedF (fLY l) domLY (FM gY gsY) envY aY dt
    htgFY htgenvY
    (path.map (fun p => (⟨fRY p, Term.const 1, domRY⟩ : RepoHop 8)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRY p (hpath p hp), by simp [Term.fv], hdomRY⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact static_hopY (fRY p) (Term.const 1) _ σ' hσ' hσ'.2)
    (hfLY l hl) hdomLY
    (Program.ode (rightBlock (fRY m) (Term.const 1)) domRY)
    (coupleY l m hl hm dt hdt hv)
    hσ
  rw [show (path.map (fun p => (⟨fRY p, Term.const 1, domRY⟩ : RepoHop 8))).map
      (fun h => h.prog domLY)
      = path.map (fun p => (⟨fRY p, Term.const 1, domRY⟩ : RepoHop 8).prog domLY)
    from by rw [List.map_map]; rfl] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono
    (List.rel_append (hops_convY path hpath)
      (List.Forall₂.cons (fun _ _ h => h) List.Forall₂.nil)) ν μ hrun) hfa

/-! ## The step provider (in-place at or ahead, climb from behind) -/

theorem HmultiY (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdY 0 0) (hv01 : VerdY 0 1) (hv02 : VerdY 0 2)
    (hv11 : VerdY 1 1) (hv12 : VerdY 1 2) (hv22 : VerdY 2 2) :
    ∀ P ∈ leftProgsY dt, ∀ (q : ℕ), q < GrY.modes.length → ∀ σ, σ mvY = (q : ℝ) →
      Formula.sat (Formula.and (FM gY gsY) envY) σ →
      ∃ segs : List (ℕ × RMode (Var 8) × REdge (Var 8)),
        (∀ s ∈ segs, GrY.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrY.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 8)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gY gsY) envY)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrY] using hq
  have hsingle : ∀ (a : ℕ × RMode (Var 8) × REdge (Var 8)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 8) × REdge (Var 8))
      (b : ℕ × RMode (Var 8) × REdge (Var 8)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 8) × REdge (Var 8)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  simp only [leftProgsY, leftDataY, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  all_goals interval_cases q
  -- window STEEP: every start couples in place
  · exact ⟨[(0, modeY 0, edgeY 0 0)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 0 (by norm_num), edgeY_mem 0 0 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 0 0 (by norm_num) (by norm_num) dt hdt hv00 [] (by simp) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(1, modeY 1, edgeY 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 1 (by norm_num), edgeY_mem 1 1 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 0 1 (by norm_num) (by norm_num) dt hdt hv01 [] (by simp) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(2, modeY 2, edgeY 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 2 (by norm_num), edgeY_mem 2 2 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 0 2 (by norm_num) (by norm_num) dt hdt hv02 [] (by simp) hσ
        simpa [modeY] using this)⟩
  -- window MODER: start STEEP climbs, the rest in place
  · exact ⟨[(0, modeY 0, edgeY 0 1), (1, modeY 1, edgeY 1 1)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrY_modeAt 0 (by norm_num), edgeY_mem 0 1 (by simp [GrY])⟩
        · exact ⟨GrY_modeAt 1 (by norm_num), edgeY_mem 1 1 (by simp [GrY])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 1 1 (by norm_num) (by norm_num) dt hdt hv11 [0]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(1, modeY 1, edgeY 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 1 (by norm_num), edgeY_mem 1 1 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 1 1 (by norm_num) (by norm_num) dt hdt hv11 [] (by simp) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(2, modeY 2, edgeY 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 2 (by norm_num), edgeY_mem 2 2 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 1 2 (by norm_num) (by norm_num) dt hdt hv12 [] (by simp) hσ
        simpa [modeY] using this)⟩
  -- window FLAT: climb to FLAT from behind, in place at FLAT
  · exact ⟨[(0, modeY 0, edgeY 0 1), (1, modeY 1, edgeY 1 2), (2, modeY 2, edgeY 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrY_modeAt 0 (by norm_num), edgeY_mem 0 1 (by simp [GrY])⟩
        · exact ⟨GrY_modeAt 1 (by norm_num), edgeY_mem 1 2 (by simp [GrY])⟩
        · exact ⟨GrY_modeAt 2 (by norm_num), edgeY_mem 2 2 (by simp [GrY])⟩),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 2 2 (by norm_num) (by norm_num) dt hdt hv22 [0, 1]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(1, modeY 1, edgeY 1 2), (2, modeY 2, edgeY 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrY_modeAt 1 (by norm_num), edgeY_mem 1 2 (by simp [GrY])⟩
        · exact ⟨GrY_modeAt 2 (by norm_num), edgeY_mem 2 2 (by simp [GrY])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 2 2 (by norm_num) (by norm_num) dt hdt hv22 [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeY] using this)⟩
  · exact ⟨[(2, modeY 2, edgeY 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrY_modeAt 2 (by norm_num), edgeY_mem 2 2 (by simp [GrY])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondY 2 2 (by norm_num) (by norm_num) dt hdt hv22 [] (by simp) hσ
        simpa [modeY] using this)⟩

/-- **`refinement_ladder_rover_rung1_2to3`, modal Theorem 3** — the first plain
list-invariant instance (multiF chain, climb dispatch, no vacuity). -/
theorem story2_lateral_rung_a_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdY 0 0) (hv01 : VerdY 0 1) (hv02 : VerdY 0 2)
    (hv11 : VerdY 1 1) (hv12 : VerdY 1 2) (hv22 : VerdY 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsY dt))
      (rightAutomatonBody GrY mvY)
      (RFormula.and (RFormula.and (canonInvM gY gsY) (envLR domLY domRY))
        (mvValidR mvY GrY.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrY mvY (FM gY gsY) domLY domRY (leftProgsY dt)
    (canonInvM gY gsY) (encode_canonInvM gY gsY) ?_ ?_ ?_
  · exact hdis_multi GrY 0 1 dt leftDataY (by decide) httY hRvY hLY
  · exact hstep_assembled_multiF GrY mvY (FM gY gsY) envY (leftProgsY dt)
      hmvFY hmvenvY hfreshY httY hltY (hframesY dt)
      (HmultiY dt hdt hv00 hv01 hv02 hv11 hv12 hv22)
  · exact hddF_multiE GrY 0 1 dt leftDataY (canonInvM gY gsY) domLY domRY (by decide)
      httY hRvY hLY
      (canonInvM_varsL gY gsY (by
        intro g' hg'
        simp only [gY, gsY, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gY gsY) hdomLY hdomRY


end Story2LateralAModal
end RelCertifier
