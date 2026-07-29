/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `refinement_ladder_rover_rung2c_6dof`, modal Theorem 3 (W5)

The one-way-chain benchmark, and three firsts at once:

* **first list-invariant (multiF-shape) instance** — the 8-conjunct lockstep
  bisimulation `vL = vR ∧ sL = sR ∧ ψL = ψR ∧ θL = θR` (as `≤`-pairs) rides `FM g gs`
  through the L6 machinery, in the cover's stratified-DC order (v, ψ, θ pairs first,
  then the s pair — the s conjunct's Lie vanishes only on the equality locus of the
  others);
* **first region-carrying (multiR) instance** — the right graph is the one-way chain
  `STEEP → MODER → FLAT`, so the three backward (window, start) pairs have no path to
  the window's landing mode; they discharge by VACUITY: the loop invariant's
  `mvRegion` conjunct pins the right execution at or beyond its mode's lower s-bound
  (forward-invariant: `s' = v·((1 − ψ²/2) − 0.3θ²) ≥ 0` on the envelope), the
  guard-gated left window (`gwindowSeg`, R2) requires the left band, and the exact
  lockstep `sL = sR` makes the two contradict — in-kernel, no Z3;
* **first 6-dimensional existence discharge** — per landing mode, the stratified
  route with `gsS` = the six strict v/ψ/θ faces, `gsN` = the five nonstrict faces
  (`s ≥ 0`, whose Lie needs the strict core, and the four zero-field z/φ faces),
  hand Lipschitz `K = 8` and field bound `L = 8` for the quadratic-bracket field.

The landing-region fact the loop's close owes (`regions (qfOf segs q)`) rides the
coupling as a NINTH invariant conjunct (`lowFace b(l) s_R`), so no post-hoc run
surgery is needed; the enriched target is then weakened into `(F ∧ env) ∧ regions l`.

Residuals: three route-verdict packs (`VerdR6 l` — 9 stratified-DC queries each, the
8 cover conjuncts plus the region face). Axioms: the standard three +
`z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Encoding.ModeRegion
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2c_6dof

namespace RelCertifier
namespace RoverRung2cModal

set_option maxHeartbeats 1600000

open DL DLCalTiming DLRel Parse Set

def vs6 : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]
def dummy6 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mL6 (l : ℕ) : Parse.PMode :=
  refinement_ladder_rover_rung2c_6dof_IR.L.modes.getD l dummy6
def mR6 (q : ℕ) : Parse.PMode :=
  refinement_ladder_rover_rung2c_6dof_IR.R.modes.getD q dummy6

abbrev mv6 : Var 6 := (Side.Aux, 0)
abbrev a6 : Fin 6 := (1 : Fin 6)
abbrev tg6 : Var 6 := (Side.Aux, a6)

noncomputable def fL6 (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs6 6 Side.L (mL6 l)
noncomputable def fR6 (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs6 6 Side.R (mR6 q)
noncomputable def domL6 : Formula (Var 6) := hostEvolve vs6 6 Side.L (mL6 0)
noncomputable def domR6 : Formula (Var 6) := hostEvolve vs6 6 Side.R (mR6 0)
noncomputable def guard6 (l : ℕ) : Formula (Var 6) := hostGuard vs6 6 Side.L (mL6 l)
noncomputable def env6 : Formula (Var 6) := Formula.and domL6 domR6

/-! ## The 8-conjunct lockstep invariant, stratified-DC order -/

/-- Atom list of a conjunction (left-nested parse shape). -/
def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def inv6PF : Parse.PForm :=
  (refinement_ladder_rover_rung2c_6dof_IR.invariants.getD 0 ("", .tt)).2

/-- The `i`-th lowered invariant conjunct (`lhs − rhs` safe-side term). -/
noncomputable def gAt (i : ℕ) : Term (Var 6) :=
  ((Run.invToG vs6 6 ((atomsOf inv6PF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

/-- Head of the DC-ordered list: the `vL ≤ vR` conjunct. -/
noncomputable def g6 : Term (Var 6) := gAt 0

/-- Tail of the DC-ordered list: `vR ≤ vL`, the ψ pair, the θ pair, then the s pair
(the cover's certified order — the s conjunct's Lie needs the equality locus of the
velocity and attitude pairs). -/
noncomputable def gs6 : List (Term (Var 6)) :=
  [gAt 1, gAt 4, gAt 5, gAt 6, gAt 7, gAt 2, gAt 3]

/-! ## The mode regions (the L4 conditioning) -/

/-- The right chain's preserved lower s-bounds: `0`, `3/5`, `7/5`. -/
noncomputable def b6 (q : ℕ) : ℝ := if q = 0 then 0 else if q = 1 then 3/5 else 7/5

/-- Mode `q`'s preserved region: `b6 q ≤ s_R`. -/
noncomputable def region6 (q : ℕ) : Formula (Var 6) :=
  Formula.cmp .le (Term.const (b6 q)) (Term.var (Rv 1))

theorem region6_fv (q : ℕ) : (region6 q).fv ⊆ range Rv := by
  intro x hx
  simp only [region6, Formula.fv, Term.fv, Set.empty_union, Set.mem_singleton_iff] at hx
  exact ⟨1, hx.symm⟩

theorem hmvreg6 : ∀ q, mv6 ∉ (region6 q).fv := fun q h =>
  absurd (region6_fv q h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## Side-splits -/

theorem fL6_pipe (l : ℕ) (i : Fin 6) : fL6 l i =
    (((some (mL6 l)).bind (Run.dynOf vs6 6 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR6_pipe (q : ℕ) (i : Fin 6) : fR6 q i =
    (((some (mR6 q)).bind (Run.dynOf vs6 6 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL6_pipe : domL6 =
    (((some (mL6 0)).bind (fun m => Run.lowerF vs6 6 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR6_pipe : domR6 =
    (((some (mR6 0)).bind (fun m => Run.lowerF vs6 6 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
/-- Guard AST repackaged in evolve position, so the evolve-shaped side lemma applies. -/
def gmode6 (l : ℕ) : Parse.PMode := ⟨"", [], .tt, (mL6 l).guard, []⟩

theorem guard6_pipe (l : ℕ) : guard6 l =
    (((some (gmode6 l)).bind (fun m => Run.lowerF vs6 6 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL6 (l : ℕ) (hl : l < 3) : ∀ i, (fL6 l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs6) (some (mL6 l))
    (by interval_cases l <;>
      simp [mL6, refinement_ladder_rover_rung2c_6dof_IR, Parse.PExpr.namesFree]) i x
    (fL6_pipe l i ▸ hx))

theorem hfR6 (q : ℕ) (hq : q < 3) : ∀ i, (fR6 q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs6) (some (mR6 q))
    (by interval_cases q <;>
      simp [mR6, refinement_ladder_rover_rung2c_6dof_IR, Parse.PExpr.namesFree]) i x
    (fR6_pipe q i ▸ hx))

theorem hdomL6 : domL6.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs6) (some (mL6 0))
    (by simp [mL6, refinement_ladder_rover_rung2c_6dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domL6_pipe ▸ hx))

theorem hdomR6 : domR6.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs6) (some (mR6 0))
    (by simp [mR6, refinement_ladder_rover_rung2c_6dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domR6_pipe ▸ hx))

theorem hguard6 (l : ℕ) (hl : l < 3) : (guard6 l).fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs6) (some (gmode6 l))
    (by interval_cases l <;>
      simp [gmode6, mL6, refinement_ladder_rover_rung2c_6dof_IR, Parse.PForm.namesFree,
        Parse.PExpr.namesFree]) x (guard6_pipe l ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg6 : ∀ g' ∈ g6 :: gs6, mv6 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg6 : ∀ g' ∈ g6 :: gs6, tg6 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvF6 : mv6 ∉ (FM g6 gs6).fv := notMem_FM_fv hmvg6

theorem htgF6 : tg6 ∉ (FM g6 gs6).fv := notMem_FM_fv htgg6

theorem hmvenv6 : mv6 ∉ env6.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomL6 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomR6 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenv6 : tg6 ∉ env6.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomL6 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomR6 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph — the one-way chain -/

noncomputable def mode6 (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR6 q) (Term.const 1), dom := domR6, weight := 1 }

def edge6 (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def Gr6 : SearchGraph (Var 6) :=
  { modes := [mode6 0, mode6 1, mode6 2],
    edges := [edge6 0 1, edge6 0 0, edge6 1 2, edge6 1 1, edge6 2 2] }

theorem Gr6_modeAt (q : ℕ) (hq : q < 3) : Gr6.modeAt q = some (mode6 q) := by
  interval_cases q <;> rfl

theorem htt6 : ∀ q, ∀ e ∈ Gr6.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ Gr6.edges := List.mem_of_mem_filter he
  simp only [Gr6, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hlt6 : ∀ q, ∀ e ∈ Gr6.edgesFrom q, e.tgt < Gr6.modes.length := by
  intro q e he
  have hmem : e ∈ Gr6.edges := List.mem_of_mem_filter he
  simp only [Gr6, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [Gr6, edge6]

theorem hRv6 : ∀ q m, Gr6.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = mode6 q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr6] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr6] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr6] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr6])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR6 q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR6 q) (Term.const 1) (hfR6 q hq3)
      (by simp [Term.fv]) hy
  · exact hdomR6 hy

theorem edge6_mem : ∀ st tgt, edge6 st tgt ∈ Gr6.edges →
    edge6 st tgt ∈ Gr6.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edge6]⟩

theorem hfresh6 : ∀ q m, Gr6.modeAt q = some m →
    mv6 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRv6 q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The guard-gated left window family -/

noncomputable def leftData6 : List (Formula (Var 6) × (Fin 6 → Term (Var 6))
    × Formula (Var 6) × ℕ) :=
  [(guard6 0, fL6 0, domL6, 1), (guard6 1, fL6 1, domL6, 1), (guard6 2, fL6 2, domL6, 1)]

noncomputable def leftProgs6 (dt : ℝ) : List (Program (Var 6)) :=
  leftData6.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg6 dt d.2.2.2)

theorem hL6 : ∀ d ∈ leftData6, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData6, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguard6 0 (by norm_num), hfL6 0 (by norm_num), hdomL6⟩
  · exact ⟨hguard6 1 (by norm_num), hfL6 1 (by norm_num), hdomL6⟩
  · exact ⟨hguard6 2 (by norm_num), hfL6 2 (by norm_num), hdomL6⟩

theorem hframes6 (dt : ℝ) : ∀ P ∈ leftProgs6 dt, FramesMv P mv6 := by
  intro P hP
  simp only [leftProgs6, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg6 dt d.2.2.2 mv6 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hq3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hqm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq1 : Run.parseRat "1" = some 1 := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hqm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hqm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq89995 : Run.parseRat "899.95" = some ((17999:ℚ)/20) := by
  have h : parseQ "899.95" = some (⟨89995, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The lowered right fields (kernel pins) -/

/-- The per-mode velocity drive: `0.30`, `0.50`, `0.65`. -/
noncomputable def cst6 (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fR6_eval0 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 0) x = 3 * (cst6 q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cst6]

theorem fR6_eval1 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 1) x = x (Rv 0) *
      ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval2 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval3 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval4 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 4) x = 0 := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval5 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 5) x = 0 := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

/-! ## The evolve faces (`--emit-viability3` census: 6 strict, 5 nonstrict) -/

noncomputable def faceVLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))
noncomputable def facePsiLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 2))
noncomputable def facePsiHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 2)) (Term.const ((3:ℝ)/20))
noncomputable def faceThLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 3))
noncomputable def faceThHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 3)) (Term.const ((3:ℝ)/20))
noncomputable def faceSLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))
noncomputable def faceZLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 4))
noncomputable def faceZHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 4)) (Term.const ((11:ℝ)/10))
noncomputable def facePhLo : Term (Var 6) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 5))
noncomputable def facePhHi : Term (Var 6) :=
  Term.binop AOp.sub (Term.var (Rv 5)) (Term.const ((3:ℝ)/5))

noncomputable def gsS6 : List (Term (Var 6)) :=
  [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi]
noncomputable def gsN6 : List (Term (Var 6)) :=
  [faceSLo, faceZLo, faceZHi, facePhLo, facePhHi]

theorem faces_fv_R6 : ∀ gT ∈ gsS6 ++ gsN6, ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  simp only [gsS6, gsN6, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi, faceSLo,
        faceZLo, faceZHi, facePhLo, facePhHi, Term.fv, Set.mem_union,
        Set.mem_empty_iff_false, false_or, or_false, Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

/-! ## The frozen-left joint field -/

theorem odeField_R6 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    odeField (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cst6 q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0) *
          ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)))
        else if c = Rv 2 then -1 * x (Rv 2)
        else if c = Rv 3 then -1 * x (Rv 3)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have h0 : (Lv j : Var 6) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      have h1 : (Lv j : Var 6) ≠ Rv 1 := by simp [Lv, Rv, Prod.ext_iff]
      have h2 : (Lv j : Var 6) ≠ Rv 2 := by simp [Lv, Rv, Prod.ext_iff]
      have h3 : (Lv j : Var 6) ≠ Rv 3 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, h0, h1, h2, h3]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fR6_eval0 q hq]
      · have h0 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR6_eval1 q hq, h0]
      · have h0 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR6_eval2 q hq, h0, h1]
      · have h0 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR6_eval3 q hq, h0, h1, h2]
      · have h0 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        have h3 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR6_eval4 q hq, h0, h1, h2, h3]
      · have h0 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        have h2 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
        have h3 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR6_eval5 q hq, h0, h1, h2, h3]
  · have hnotR : ∀ j : Fin 6, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1),
      if_neg (hnotR 2), if_neg (hnotR 3)]

/-! ## The evolve/guard shapes -/

theorem sat_domR6 (x : State (Var 6)) : Formula.sat domR6 x ↔
    (-(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/20 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 4) ∧ x (Rv 4) ≤ 11/10) := by
  simp only [domR6, hostEvolve, mR6, refinement_ladder_rover_rung2c_6dof_IR, vs6]
  simp [Run.lowerF, Run.lowerE, hqm05, hq06, hq015, hq00, hq08, hqm10, hq11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  push_cast
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩

theorem sat_guard6_0 (x : State (Var 6)) : Formula.sat (guard6 0) x ↔
    (0 ≤ x (Lv 1) ∧ x (Lv 1) < 3/5) := by
  simp only [guard6, hostGuard, mL6, refinement_ladder_rover_rung2c_6dof_IR, vs6]
  simp [Run.lowerF, Run.lowerE, hq00, hq06, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_guard6_1 (x : State (Var 6)) : Formula.sat (guard6 1) x ↔
    (3/5 ≤ x (Lv 1) ∧ x (Lv 1) < 7/5) := by
  simp only [guard6, hostGuard, mL6, refinement_ladder_rover_rung2c_6dof_IR, vs6]
  simp [Run.lowerF, Run.lowerE, hq06, hq14, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_guard6_2 (x : State (Var 6)) : Formula.sat (guard6 2) x ↔
    (7/5 ≤ x (Lv 1) ∧ x (Lv 1) < 17999/20) := by
  simp only [guard6, hostGuard, mL6, refinement_ladder_rover_rung2c_6dof_IR, vs6]
  simp [Run.lowerF, Run.lowerE, hq14, hq89995, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

/-! ## The lowered invariant conjuncts (kernel pins for the s pair and the v pair) -/

theorem gAt2_eval (x : State (Var 6)) : Term.eval (gAt 2) x = x (Lv 1) - x (Rv 1) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, inv6PF, refinement_ladder_rover_rung2c_6dof_IR, Run.invToG,
    Run.lowerE, vs6, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt3_eval (x : State (Var 6)) : Term.eval (gAt 3) x = x (Rv 1) - x (Lv 1) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, inv6PF, refinement_ladder_rover_rung2c_6dof_IR, Run.invToG,
    Run.lowerE, vs6, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-- The exact-lockstep position equality, extracted from the loop invariant. -/
theorem lockstep_s {σ : State (Var 6)} (hF : Formula.sat (FM g6 gs6) σ) :
    σ (Lv 1) = σ (Rv 1) := by
  have hall := (sat_FM_iff g6 gs6 σ).mp hF
  have h2 : Term.eval (gAt 2) σ ≤ 0 := hall (gAt 2) (by simp [gs6])
  have h3 : Term.eval (gAt 3) σ ≤ 0 := hall (gAt 3) (by simp [gs6])
  rw [gAt2_eval] at h2
  rw [gAt3_eval] at h3
  linarith

/-! ## Strict inflow on the six strict faces -/

theorem hbndS6 (q : ℕ) (hq : q < 3) : ∀ gT ∈ gsS6, ∀ x : State (Var 6),
    Term.eval gT x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1))
      (fun ω => Term.eval gT ω) x < 0 := by
  have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have h30 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h31 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have h32 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  intro gT hgT x hface
  simp only [gsS6, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl
  · -- faceVLo: v = 0 ⟹ Lie = −3·cst < 0
    have hx0 : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cst6]
  · -- faceVHi: v = 4/5 ⟹ Lie = 3(cst − 4/5) < 0
    have hx0 : x (Rv 0) = 4/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-(4/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(4/5)) x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cst6]
  · -- facePsiLo: ψ = −1/2 ⟹ Lie = ψ = −1/2 < 0
    have hx2 : x (Rv 2) = -(1:ℝ)/2 := by
      simp only [facePsiLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval facePsiLo ω)
        = fun y => (-1 : ℝ) * y (Rv 2) + (-(1/2)) := by
      funext y; simp [facePsiLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) (-1) (-(1/2)) x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, hx2]
    norm_num
  · -- facePsiHi: ψ = 3/20 ⟹ Lie = −ψ = −3/20 < 0
    have hx2 : x (Rv 2) = (3:ℝ)/20 := by
      simp only [facePsiHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval facePsiHi ω)
        = fun y => (1 : ℝ) * y (Rv 2) + (-(3/20)) := by
      funext y; simp [facePsiHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) 1 (-(3/20)) x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, hx2]
    norm_num
  · -- faceThLo
    have hx3 : x (Rv 3) = -(1:ℝ)/2 := by
      simp only [faceThLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 3) + (-(1/2)) := by
      funext y; simp [faceThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) (-1) (-(1/2)) x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl, hx3]
    norm_num
  · -- faceThHi
    have hx3 : x (Rv 3) = (3:ℝ)/20 := by
      simp only [faceThHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 6) => Term.eval faceThHi ω)
        = fun y => (1 : ℝ) * y (Rv 3) + (-(3/20)) := by
      funext y; simp [faceThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) 1 (-(3/20)) x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl, hx3]
    norm_num

/-! ## Nonpositive Lie on the five nonstrict faces -/

theorem hbndN6 (q : ℕ) (hq : q < 3) : ∀ i (hi : i < gsN6.length), ∀ x : State (Var 6),
    (∀ gT' ∈ gsS6 ++ ([] : List (Term (Var 6))), Term.eval gT' x ≤ 0) →
    Lie (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1))
      (fun ω => Term.eval gsN6[i] ω) x ≤ 0 := by
  have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h40 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h41 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have h42 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  have h43 : (Rv (4 : Fin 6) : Var 6) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
  have h50 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have h51 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have h52 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
  have h53 : (Rv (5 : Fin 6) : Var 6) ≠ Rv 3 := by simp [Rv, Prod.ext_iff]
  intro i hi x hx
  have hi5 : i < 5 := by simpa [gsN6] using hi
  have hv0 : 0 ≤ x (Rv 0) := by
    have := hx faceVLo (List.mem_append_left _ (by simp [gsS6]))
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
    have := hx facePsiLo (List.mem_append_left _ (by simp [gsS6]))
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hp2 : x (Rv 2) ≤ 3/20 := by
    have := hx facePsiHi (List.mem_append_left _ (by simp [gsS6]))
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have ht1 : -(1:ℝ)/2 ≤ x (Rv 3) := by
    have := hx faceThLo (List.mem_append_left _ (by simp [gsS6]))
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have ht2 : x (Rv 3) ≤ 3/20 := by
    have := hx faceThHi (List.mem_append_left _ (by simp [gsS6]))
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  interval_cases i
  · -- faceSLo: Lie = −(v·B), v ≥ 0 and B ≥ 4/5 on the strict core
    show Lie _ (fun ω => Term.eval faceSLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceSLo ω)
        = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [faceSLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
      odeField_R6 q hq]
    simp only [eq_self_iff_true, if_true, if_neg h10, if_pos rfl]
    have hB : (0:ℝ) ≤ (1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3)) := by
      nlinarith [sq_nonneg (x (Rv 2)), sq_nonneg (x (Rv 3))]
    have := mul_nonneg hv0 hB
    linarith
  · show Lie _ (fun ω => Term.eval faceZLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceZLo ω)
        = fun y => (-1 : ℝ) * y (Rv 4) + (-1) := by
      funext y; simp [faceZLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) (-1) (-1) x,
      odeField_R6 q hq]
    simp only [if_neg h40, if_neg h41, if_neg h42, if_neg h43]
    norm_num
  · show Lie _ (fun ω => Term.eval faceZHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval faceZHi ω)
        = fun y => (1 : ℝ) * y (Rv 4) + (-(11/10)) := by
      funext y; simp [faceZHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) 1 (-(11/10)) x,
      odeField_R6 q hq]
    simp only [if_neg h40, if_neg h41, if_neg h42, if_neg h43]
    norm_num
  · show Lie _ (fun ω => Term.eval facePhLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval facePhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 5) + (-(1/2)) := by
      funext y; simp [facePhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) (-1) (-(1/2)) x,
      odeField_R6 q hq]
    simp only [if_neg h50, if_neg h51, if_neg h52, if_neg h53]
    norm_num
  · show Lie _ (fun ω => Term.eval facePhHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 6) => Term.eval facePhHi ω)
        = fun y => (1 : ℝ) * y (Rv 5) + (-(3/5)) := by
      funext y; simp [facePhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) 1 (-(3/5)) x,
      odeField_R6 q hq]
    simp only [if_neg h50, if_neg h51, if_neg h52, if_neg h53]
    norm_num

/-! ## Hand Lipschitz and field bounds (`K = L = 8` on unit balls) -/

theorem hLip6 (q : ℕ) (hq : q < 3) (ν : State (Var 6))
    (hν : ∀ gT ∈ gsS6, Term.eval gT ν ≤ 0) :
    LipschitzOnWith 8 (odeField (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  have hν0lo : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsS6])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν0hi : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsS6])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hν2lo : -(1:ℝ)/2 ≤ ν (Rv 2) := by
    have := hν facePsiLo (by simp [gsS6])
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hν2hi : ν (Rv 2) ≤ 3/20 := by
    have := hν facePsiHi (by simp [gsS6])
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have hν3lo : -(1:ℝ)/2 ≤ ν (Rv 3) := by
    have := hν faceThLo (by simp [gsS6])
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have hν3hi : ν (Rv 3) ≤ 3/20 := by
    have := hν faceThHi (by simp [gsS6])
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_R6 q hq, odeField_R6 q hq]
  rw [Metric.mem_closedBall] at hx hy
  have hcb : ∀ (w : State (Var 6)), dist w ν ≤ 1 → ∀ j : Fin 6,
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
  have hdc : ∀ j : Fin 6, |x (Rv j) - y (Rv j)| ≤ dist x y := by
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
    have hdiff : 3 * (cst6 q - x (Rv 0)) - 3 * (cst6 q - y (Rv 0))
        = -3 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have h0 := hdc 0
    have habs : |(-3 : ℝ)| = 3 := by norm_num
    rw [habs, hcoe]
    nlinarith
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
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
    have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 2) - -1 * y (Rv 2) = -(x (Rv 2) - y (Rv 2)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 2
    nlinarith
  by_cases hc3 : c = Rv 3
  · subst hc3
    have h30 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h31 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h32 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : -1 * x (Rv 3) - -1 * y (Rv 3) = -(x (Rv 3) - y (Rv 3)) := by ring
    rw [hdiff, abs_neg, hcoe]
    have := hdc 3
    nlinarith
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc3]
    simp [dist_nonneg]

theorem hfbnd6 (q : ℕ) (hq : q < 3) (ν : State (Var 6))
    (hν : ∀ gT ∈ gsS6, Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fR6 q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  intro x hx
  have hν0lo : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsS6])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν0hi : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsS6])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hν2lo : -(1:ℝ)/2 ≤ ν (Rv 2) := by
    have := hν facePsiLo (by simp [gsS6])
    simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
  have hν2hi : ν (Rv 2) ≤ 3/20 := by
    have := hν facePsiHi (by simp [gsS6])
    simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have hν3lo : -(1:ℝ)/2 ≤ ν (Rv 3) := by
    have := hν faceThLo (by simp [gsS6])
    simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
  have hν3hi : ν (Rv 3) ≤ 3/20 := by
    have := hν faceThHi (by simp [gsS6])
    simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  rw [Metric.mem_closedBall] at hx
  have hcb : ∀ j : Fin 6, |x (Rv j) - ν (Rv j)| ≤ 1 := by
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
  rw [odeField_R6 q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cst6 q ∧ cst6 q ≤ 13/20 := by
      interval_cases q <;> norm_num [cst6]
    rw [abs_le]
    push_cast
    obtain ⟨hc1, hc2⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hx0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
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
    have h20 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h21 : (Rv (2 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h20, if_neg h21, if_pos rfl, Real.norm_eq_abs]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hx2, abs_nonneg (x (Rv 2))]
  by_cases hc3 : c = Rv 3
  · subst hc3
    have h30 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    have h31 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
    have h32 : (Rv (3 : Fin 6) : Var 6) ≠ Rv 2 := by simp [Rv, Prod.ext_iff]
    simp only [eq_self_iff_true, if_true, if_neg h30, if_neg h31, if_neg h32, if_pos rfl, Real.norm_eq_abs]
    rw [abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hx3, abs_nonneg (x (Rv 3))]
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc3]
    norm_num

/-! ## The existence discharge (per landing mode, Z3-free) -/

theorem esR6 (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM g6 gs6) env6) σ →
      HExistSegB (fL6 l) (fR6 l) (Term.const 1) domL6 domR6 dt
        (Function.update σ tg6 0) := by
  intro σ hσ
  have hR : Formula.sat domR6 σ := hσ.2.2
  rw [sat_domR6] at hR
  obtain ⟨h5lo, h5hi, h2lo, h2hi, h1lo, h3lo, h3hi, h0lo, h0hi, h4lo, h4hi⟩ := hR
  have hupd : ∀ j : Fin 6, σ (Side.R, j) = Function.update σ tg6 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tg6, Prod.ext_iff])]
  have hfS : ∀ gT ∈ gsS6, Term.eval gT (Function.update σ tg6 0) ≤ 0 := by
    intro gT hgT
    simp only [gsS6, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT ∈ gsN6, Term.eval gT (Function.update σ tg6 0) ≤ 0 := by
    intro gT hgT
    simp only [gsN6, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratified (fL6 l) (fR6 l) (Term.const 1)
    domL6 domR6 gsS6 [] gsN6 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL6 l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_R6 gT (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL6 l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_R6 gT (List.mem_append_right _ hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x _ hface
      exact hbndS6 l hl gT hgT x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      exact hbndN6 l hl i hi x hx)
    (by
      intro x hS hN
      have hS' : ∀ gT ∈ gsS6, Term.eval gT x ≤ 0 :=
        fun gT hgT => hS gT (List.mem_append_left _ hgT)
      have hv0 : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsS6])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hv1 : x (Rv 0) ≤ 4/5 := by
        have := hS' faceVHi (by simp [gsS6])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsS6])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hp2 : x (Rv 2) ≤ 3/20 := by
        have := hS' facePsiHi (by simp [gsS6])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have ht1 : -(1:ℝ)/2 ≤ x (Rv 3) := by
        have := hS' faceThLo (by simp [gsS6])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have ht2 : x (Rv 3) ≤ 3/20 := by
        have := hS' faceThHi (by simp [gsS6])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hs0 : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsN6])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hz1 : -(1:ℝ) ≤ x (Rv 4) := by
        have := hN faceZLo (by simp [gsN6])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hz2 : x (Rv 4) ≤ 11/10 := by
        have := hN faceZHi (by simp [gsN6])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hf1 : -(1:ℝ)/2 ≤ x (Rv 5) := by
        have := hN facePhLo (by simp [gsN6])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hf2 : x (Rv 5) ≤ 3/5 := by
        have := hN facePhHi (by simp [gsN6])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      exact (sat_domR6 x).mpr ⟨hf1, hf2, hp1, hp2, hs0, ht1, ht2, hv0, hv1, hz1, hz2⟩)
    8 8 1 one_pos
    (fun ν0 h0 => hLip6 l hl ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    (fun ν0 h0 => hfbnd6 l hl ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tg6 0)
    hfS
    hfN
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The route-verdict residuals (stratified-DC, 9 queries per window) -/

/-- The coupling's invariant tail: the 7 DC-ordered conjuncts plus the window's
region face (`b6 l − s_R`) as the ninth component. -/
noncomputable def gs9 (l : ℕ) : List (Term (Var 6)) :=
  gs6 ++ [lowFace (b6 l) (Rv 1)]

def VerdR6 (l : ℕ) : Prop :=
  ∀ i (hi : i < (g6 :: gs9 l).length),
    z3solve (flowQuery ⟨(g6 :: gs9 l)[i], fL6 l, fR6 l, Term.const 1,
      strataDomHost (Formula.and domL6 domR6) ((g6 :: gs9 l).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(g6 :: gs9 l)[i], fL6 l, fR6 l, Term.const 1,
      strataDomHost (Formula.and domL6 domR6) ((g6 :: gs9 l).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(g6 :: gs9 l)[i], fL6 l, fR6 l, Term.const 1,
      strataDomHost (Formula.and domL6 domR6) ((g6 :: gs9 l).take i)⟩) = Verdict.unsat

theorem htggs9 (l : ℕ) : ∀ g' ∈ g6 :: gs9 l, tg6 ∉ g'.fv := by
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact htgg6 g6 List.mem_cons_self
  · rcases List.mem_append.mp hg' with hg' | hg'
    · exact htgg6 g' (List.mem_cons_of_mem _ hg')
    · rw [List.mem_singleton] at hg'
      subst hg'
      intro h
      simp only [lowFace, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
        Set.mem_singleton_iff] at h
      exact absurd h (by simp [tg6, Rv, Prod.ext_iff])

theorem htgF9 (l : ℕ) : tg6 ∉ (FM g6 (gs9 l)).fv :=
  notMem_FM_fv (htggs9 l)

theorem FM_drop9 (l : ℕ) {ν : State (Var 6)}
    (h : Formula.sat (FM g6 (gs9 l)) ν) : Formula.sat (FM g6 gs6) ν := by
  rw [sat_FM_iff] at h ⊢
  intro g' hg'
  refine h g' ?_
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hg')

theorem FM_add9 (l : ℕ) {ν : State (Var 6)}
    (h : Formula.sat (FM g6 gs6) ν) (hb : b6 l ≤ ν (Rv 1)) :
    Formula.sat (FM g6 (gs9 l)) ν := by
  rw [sat_FM_iff] at h ⊢
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact h g6 List.mem_cons_self
  · rcases List.mem_append.mp hg' with hg' | hg'
    · exact h g' (List.mem_cons_of_mem _ hg')
    · rw [List.mem_singleton] at hg'
      subst hg'
      rw [eval_lowFace]
      linarith

theorem sat_region6_iff (q : ℕ) (ν : State (Var 6)) :
    Formula.sat (region6 q) ν ↔ b6 q ≤ ν (Rv 1) := by
  simp [region6, Formula.sat, CompOp.interp, Term.eval]

/-! ## Post-weakening for `faModal` -/

theorem sat_faModal_monoPost {P Q : Program (Var 6)} {A B : Formula (Var 6)}
    {σ : State (Var 6)} (himp : ∀ ν, Formula.sat A ν → Formula.sat B ν)
    (h : Formula.sat (faModal (Equiv.refl (Var 6)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hsem, hA⟩ := h ν hν
  exact ⟨μ, hsem, himp μ hA⟩

/-! ## The coupling (enriched nine-component invariant) -/

theorem couple6 (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdR6 l) :
    ∀ σ', Formula.sat (Formula.and (FM g6 (gs9 l)) env6) σ' → σ' tg6 = 0 →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tg6 (leftBlock (fL6 l))) domL6)
        (Program.ode (rightBlock (fR6 l) (Term.const 1)) domR6)
        (Formula.and (FM g6 (gs9 l)) env6) tg6 dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tg6 (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tg6
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fL6 l) (fR6 l) (Term.const 1)
    (Formula.and domL6 domR6) (g6 :: gs9 l) hv
  have hboxes : ∀ g' ∈ g6 :: gs9 l, Formula.sat (Formula.box (Program.ode
      (leftBlock (fL6 l) ++ rightBlock (fR6 l) (Term.const 1))
      (Formula.and domL6 domR6)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff g6 (gs9 l) σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list g6 (gs9 l) (fL6 l) (fR6 l)
    (Term.const 1) domL6 domR6 tg6 dt
    (LR_blocks_disjoint _ _ _ (hfL6 l hl) (hfR6 l hl) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomL6 hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomR6 hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL6 l) _ h
      exact aux_ne_Lv a6 i hi)
    (fun h => aux_notin_range_Lv a6 (leftBlock_readVars_sub (fL6 l) (hfL6 l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fR6 l) (Term.const 1) _ h
      exact aux_ne_Rv a6 i hi)
    (fun h => aux_notin_range_Rv a6 (rightBlock_readVars_sub (fR6 l) (Term.const 1)
      (hfR6 l hl) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv a6 (rightBlock_boundSet_sub (fR6 l) (Term.const 1) h))
    (fun h => aux_notin_range_Lv a6 (hdomL6 h))
    (fun h => aux_notin_range_Rv a6 (hdomR6 h))
    (htggs9 l) hboxes
    (esR6 l hl dt hdt σ' ⟨FM_drop9 l hσ'.1, hσ'.2⟩)
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domL6 ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domR6 μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domL6 μ := by
    rwa [(Formula.coincidence domL6 (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomL6 hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fR6 l) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domL6 μ ↔ Formula.sat domL6 ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Static hops and the hop-program conversion -/

theorem static_hop6 (fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6))
    (φ : Formula (Var 6)) (σ : State (Var 6)) (hσφ : Formula.sat φ σ)
    (hdom : Formula.sat (Formula.and domL6 domR6) σ) :
    ∃ ρ, Program.sem ((⟨fR, lam, domR6⟩ : RepoHop 6).prog domL6) σ ρ
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

theorem hops_conv6 : ∀ (ps : List ℕ), (∀ p ∈ ps, p < 3) →
    List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ → Program.sem q ν μ)
      (ps.map (fun p => (⟨fR6 p, Term.const 1, domR6⟩ : RepoHop 6).prog domL6))
      (ps.map (fun p => Program.ode (rightBlock (fR6 p) (Term.const 1)) domR6)) := by
  intro ps
  induction ps with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hps
      refine List.Forall₂.cons ?_ (ih (fun p hp => hps p (List.mem_cons_of_mem a hp)))
      intro ν μ hrun
      exact joint_run_toR (hfR6 a (hps a List.mem_cons_self)) (by simp [Term.fv]) hrun

/-! ## The window response (hops to the landing terrain, coupled piece there) -/

theorem respond6 (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdR6 l)
    (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 6)} (hσE : Formula.sat (Formula.and (FM g6 (gs9 l)) env6) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (windowSeg (leftBlock (fL6 l)) domL6 tg6 dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fR6 p) (Term.const 1))
          domR6))
        ++ [Program.ode (rightBlock (fR6 l) (Term.const 1)) domR6]))
      (Formula.and (Formula.and (FM g6 gs6) env6) (region6 l))) σ := by
  have hfa := Hmulti_window1_prefixedF (fL6 l) domL6 (FM g6 (gs9 l)) env6 a6 dt
    (htgF9 l) htgenv6
    (path.map (fun p => (⟨fR6 p, Term.const 1, domR6⟩ : RepoHop 6)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfR6 p (hpath p hp), by simp [Term.fv], hdomR6⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact static_hop6 (fR6 p) (Term.const 1) _ σ' hσ' hσ'.2)
    (hfL6 l hl) hdomL6
    (Program.ode (rightBlock (fR6 l) (Term.const 1)) domR6)
    (couple6 l hl dt hdt hv)
    hσE
  rw [show (path.map (fun p => (⟨fR6 p, Term.const 1, domR6⟩ : RepoHop 6))).map
      (fun h => h.prog domL6)
      = path.map (fun p => (⟨fR6 p, Term.const 1, domR6⟩ : RepoHop 6).prog domL6)
    from by rw [List.map_map]; rfl] at hfa
  have hfa2 := sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono
    (List.rel_append (hops_conv6 path hpath)
      (List.Forall₂.cons (fun _ _ h => h) List.Forall₂.nil)) ν μ hrun) hfa
  refine sat_faModal_monoPost ?_ hfa2
  intro ν hν
  refine ⟨⟨FM_drop9 l hν.1, hν.2⟩, ?_⟩
  rw [sat_region6_iff]
  have hface := (sat_FM_iff g6 (gs9 l) ν).mp hν.1 (lowFace (b6 l) (Rv 1))
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  rw [eval_lowFace] at hface
  linarith

/-! ## The step provider — three vacuous pairs in-kernel, six climbs -/

theorem Hmulti6 (dt : ℝ) (hdt : 0 ≤ dt)
    (hv0 : VerdR6 0) (hv1 : VerdR6 1) (hv2 : VerdR6 2) :
    ∀ P ∈ leftProgs6 dt, ∀ (q : ℕ), q < Gr6.modes.length → ∀ σ, σ mv6 = (q : ℝ) →
      Formula.sat (Formula.and (FM g6 gs6) env6) σ → Formula.sat (region6 q) σ →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, Gr6.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr6.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM g6 gs6) env6)
            (region6 (qfOf segs q)))) σ := by
  intro P hP q hq σ hmv hσ hreg
  have hq3 : q < 3 := by simpa [Gr6] using hq
  have hlk : σ (Lv 1) = σ (Rv 1) := lockstep_s hσ.1
  have hb : b6 q ≤ σ (Rv 1) := (sat_region6_iff q σ).mp hreg
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
  simp only [leftProgs6, leftData6, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  -- the gate: reduce a gwindow obligation to a windowSeg one (or to vacuity)
  have hgate : ∀ (l : ℕ) (R : Program (Var 6)) (ψ : Formula (Var 6)),
      (Formula.sat (guard6 l) σ →
        Formula.sat (faModal (Equiv.refl (Var 6))
          (windowSeg (leftBlock (fL6 l)) domL6 tg6 dt 1) R ψ) σ) →
      Formula.sat (faModal (Equiv.refl (Var 6))
        (gwindowSeg (guard6 l) (leftBlock (fL6 l)) domL6 tg6 dt 1) R ψ) σ := by
    intro l R ψ hbody
    refine faModal_seqL _ _ _ _ _ _ ?_
    rw [sat_box]
    intro ν hν
    rw [sem_test] at hν
    obtain ⟨rfl, hguard⟩ := hν
    exact hbody hguard
  rcases hP with rfl | rfl | rfl
  -- window STEEP
  · interval_cases q
    · -- start STEEP: self piece
      refine ⟨[(0, mode6 0, edge6 0 0)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨Gr6_modeAt 0 (by norm_num), edge6_mem 0 0 (by simp [Gr6])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 0 _ _ ?_
      intro hguard
      rw [sat_guard6_0] at hguard
      have hbl : b6 0 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 0 (by norm_num) dt hdt hv0 [] (by simp)
        ⟨FM_add9 0 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp
    · -- start MODER against window STEEP: vacuous (region 3/5 ≤ s_R = s_L < 3/5)
      refine ⟨[], by simp, by simp, by simp, ?_⟩
      refine hgate 0 _ _ ?_
      intro hguard
      rw [sat_guard6_0] at hguard
      exfalso
      have : (3:ℝ)/5 ≤ σ (Rv 1) := by simpa [b6] using hb
      rw [← hlk] at this
      linarith [hguard.2]
    · -- start FLAT against window STEEP: vacuous
      refine ⟨[], by simp, by simp, by simp, ?_⟩
      refine hgate 0 _ _ ?_
      intro hguard
      rw [sat_guard6_0] at hguard
      exfalso
      have : (7:ℝ)/5 ≤ σ (Rv 1) := by simpa [b6] using hb
      rw [← hlk] at this
      linarith [hguard.2]
  -- window MODER
  · interval_cases q
    · -- start STEEP: hop to MODER, piece there
      refine ⟨[(0, mode6 0, edge6 0 1), (1, mode6 1, edge6 1 1)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨Gr6_modeAt 0 (by norm_num), edge6_mem 0 1 (by simp [Gr6])⟩
          · exact ⟨Gr6_modeAt 1 (by norm_num), edge6_mem 1 1 (by simp [Gr6])⟩),
        hstep _ _ _ rfl (hsingle _),
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 1 _ _ ?_
      intro hguard
      rw [sat_guard6_1] at hguard
      have hbl : b6 1 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 1 (by norm_num) dt hdt hv1 [0]
        (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num)
        ⟨FM_add9 1 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp
    · -- start MODER: self piece
      refine ⟨[(1, mode6 1, edge6 1 1)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨Gr6_modeAt 1 (by norm_num), edge6_mem 1 1 (by simp [Gr6])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 1 _ _ ?_
      intro hguard
      rw [sat_guard6_1] at hguard
      have hbl : b6 1 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 1 (by norm_num) dt hdt hv1 [] (by simp)
        ⟨FM_add9 1 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp
    · -- start FLAT against window MODER: vacuous
      refine ⟨[], by simp, by simp, by simp, ?_⟩
      refine hgate 1 _ _ ?_
      intro hguard
      rw [sat_guard6_1] at hguard
      exfalso
      have : (7:ℝ)/5 ≤ σ (Rv 1) := by simpa [b6] using hb
      rw [← hlk] at this
      linarith [hguard.2]
  -- window FLAT
  · interval_cases q
    · -- start STEEP: two hops, piece at FLAT
      refine ⟨[(0, mode6 0, edge6 0 1), (1, mode6 1, edge6 1 2), (2, mode6 2, edge6 2 2)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl
          · exact ⟨Gr6_modeAt 0 (by norm_num), edge6_mem 0 1 (by simp [Gr6])⟩
          · exact ⟨Gr6_modeAt 1 (by norm_num), edge6_mem 1 2 (by simp [Gr6])⟩
          · exact ⟨Gr6_modeAt 2 (by norm_num), edge6_mem 2 2 (by simp [Gr6])⟩),
        hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 2 _ _ ?_
      intro hguard
      rw [sat_guard6_2] at hguard
      have hbl : b6 2 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 2 (by norm_num) dt hdt hv2 [0, 1]
        (by
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> norm_num)
        ⟨FM_add9 2 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp
    · -- start MODER: one hop, piece at FLAT
      refine ⟨[(1, mode6 1, edge6 1 2), (2, mode6 2, edge6 2 2)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨Gr6_modeAt 1 (by norm_num), edge6_mem 1 2 (by simp [Gr6])⟩
          · exact ⟨Gr6_modeAt 2 (by norm_num), edge6_mem 2 2 (by simp [Gr6])⟩),
        hstep _ _ _ rfl (hsingle _),
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 2 _ _ ?_
      intro hguard
      rw [sat_guard6_2] at hguard
      have hbl : b6 2 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 2 (by norm_num) dt hdt hv2 [1]
        (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num)
        ⟨FM_add9 2 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp
    · -- start FLAT: self piece
      refine ⟨[(2, mode6 2, edge6 2 2)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨Gr6_modeAt 2 (by norm_num), edge6_mem 2 2 (by simp [Gr6])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        ?_⟩
      refine hgate 2 _ _ ?_
      intro hguard
      rw [sat_guard6_2] at hguard
      have hbl : b6 2 ≤ σ (Rv 1) := by
        rw [← hlk]
        simpa [b6] using hguard.1
      have hresp := respond6 2 (by norm_num) dt hdt hv2 [] (by simp)
        ⟨FM_add9 2 hσ.1 hbl, hσ.2⟩
      simpa [mode6, qfOf, edge6] using hresp

/-! ## The assembly -/

theorem hdis6 (dt : ℝ) :
    Disjoint (Program.vars (bigChoice (leftProgs6 dt)))
      (Program.vars ((rightAutomatonBody Gr6 mv6).rename (Equiv.refl (Var 6)))) := by
  refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
  · refine vars_bigChoice_sub _ _ ?_
    intro p hp
    simp only [leftProgs6, List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL6 d hd).1
      (hL6 d hd).2.1 (hL6 d hd).2.2
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyU_sub Gr6 _ htt6 hRv6 hx with hx | hx
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
    · exact Or.inr hx

/-- **`refinement_ladder_rover_rung2c_6dof`, modal Theorem 3** — the one-way chain,
guard-gated windows, region-carrying loop invariant, three vacuous pairs in-kernel.
Residuals: three stratified-DC verdict packs. -/
theorem rover_rung2c_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (hv0 : VerdR6 0) (hv1 : VerdR6 1) (hv2 : VerdR6 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs6 dt))
      (rightAutomatonBody Gr6 mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvRegionR mv6 region6 Gr6.modes.length))) := by
  refine theorem3_faithful_multiR_LR Gr6 mv6 (FM g6 gs6) domL6 domR6 region6
    (leftProgs6 dt) (canonInvM g6 gs6) (encode_canonInvM g6 gs6) ?_ ?_ ?_
  · exact hdis6 dt
  · exact hstep_assembled_multiR Gr6 mv6 (FM g6 gs6) (Formula.and domL6 domR6) region6
      (leftProgs6 dt) hmvF6 hmvenv6 hmvreg6 hfresh6 htt6 hlt6 (hframes6 dt)
      (Hmulti6 dt hdt hv0 hv1 hv2)
  · exact hddF_multiR Gr6 0 1 dt leftData6 region6 (canonInvM g6 gs6) domL6 domR6
      (by decide) htt6 hRv6 hL6 (fun q _ => region6_fv q)
      (canonInvM_varsL g6 gs6 (by
        intro g' hg'
        simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR g6 gs6) hdomL6 hdomR6

end RoverRung2cModal
end RelCertifier
