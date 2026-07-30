/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `refinement_ladder_rover_rung2b_6dof`, modal Theorem 3 (multiF, CATCH-UP, n = 6)

The combined-coordinate catch-up form: the declared invariant (identical in all
three modes) is `(s_L − s_R − 0.2) + (v_L − v_R)/3 ≤ 0`, i.e. a bound on the
combined coordinate `g₂ = s + v/3`. Along the right's FLAT hold the Lie of `g₂`
is EXACTLY `0.65` (`ṡ + v̇/3 = v + (0.65 − v) = 0.65` — the asymptotic `v`-row
cancels), so an explicit exponential witness flow gains `0.65·τ` in `g₂`
precisely. Along any left window `Lie g₂ = v·((1−ψ²/2)−0.3θ²) + (c_l − v) ≤
c_l ≤ 0.65` on the evolve domain (`v ≥ 0` kills the drag terms), so
`windowSeg_growth` bounds the left's gain by `0.65·(2·dt)`. With `τ = 2·dt`
the endpoint arithmetic closes the invariant with zero slack needed. The extra
`z`/`phi_r` coordinates are spectators: frozen on the right, bounded decays on
the left, and never mentioned by the invariant.

Residuals: NONE. Z3-free — axioms are exactly the standard three.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2b_6dof

namespace RelCertifier
namespace RoverRung2b6dofModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 12800000

def vsB2 : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]
def dummyB2 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLB2 (l : ℕ) : Parse.PMode := refinement_ladder_rover_rung2b_6dof_IR.L.modes.getD l dummyB2
def mRB2 (q : ℕ) : Parse.PMode := refinement_ladder_rover_rung2b_6dof_IR.R.modes.getD q dummyB2

abbrev mvB2 : Var 6 := (Side.Aux, 0)
abbrev aB2 : Fin 6 := (1 : Fin 6)
abbrev tgB2 : Var 6 := (Side.Aux, aB2)

noncomputable def fLB2 (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsB2 6 Side.L (mLB2 l)
noncomputable def fRB2 (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsB2 6 Side.R (mRB2 q)
noncomputable def domLB2 : Formula (Var 6) := hostEvolve vsB2 6 Side.L (mLB2 0)
noncomputable def domRB2 : Formula (Var 6) := hostEvolve vsB2 6 Side.R (mRB2 0)
noncomputable def envB2 : Formula (Var 6) := Formula.and domLB2 domRB2

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invB2PF : Parse.PForm :=
  (refinement_ladder_rover_rung2b_6dof_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 6) :=
  ((Run.invToG vsB2 6 ((atomsOf invB2PF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gB2 : Term (Var 6) := gAt 0
noncomputable def gsB2 : List (Term (Var 6)) := []

/-! ## Side-splits -/

theorem fLB2_pipe (l : ℕ) (i : Fin 6) : fLB2 l i =
    (((some (mLB2 l)).bind (Run.dynOf vsB2 6 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRB2_pipe (q : ℕ) (i : Fin 6) : fRB2 q i =
    (((some (mRB2 q)).bind (Run.dynOf vsB2 6 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLB2_pipe : domLB2 =
    (((some (mLB2 0)).bind (fun m => Run.lowerF vsB2 6 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRB2_pipe : domRB2 =
    (((some (mRB2 0)).bind (fun m => Run.lowerF vsB2 6 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLB2 (l : ℕ) (hl : l < 3) : ∀ i, (fLB2 l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsB2) (some (mLB2 l))
    (by interval_cases l <;>
      simp [mLB2, refinement_ladder_rover_rung2b_6dof_IR, Parse.PExpr.namesFree]) i x
    (fLB2_pipe l i ▸ hx))

theorem hfRB2 (q : ℕ) (hq : q < 3) : ∀ i, (fRB2 q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsB2) (some (mRB2 q))
    (by interval_cases q <;>
      simp [mRB2, refinement_ladder_rover_rung2b_6dof_IR, Parse.PExpr.namesFree]) i x
    (fRB2_pipe q i ▸ hx))

theorem hdomLB2 : domLB2.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsB2) (some (mLB2 0))
    (by simp [mLB2, refinement_ladder_rover_rung2b_6dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLB2_pipe ▸ hx))

theorem hdomRB2 : domRB2.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsB2) (some (mRB2 0))
    (by simp [mRB2, refinement_ladder_rover_rung2b_6dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRB2_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gB2 :: gsB2, mvB2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gB2 :: gsB2, tgB2 ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFB2 : mvB2 ∉ (FM gB2 gsB2).fv := notMem_FM_fv hmvg
theorem htgFB2 : tgB2 ∉ (FM gB2 gsB2).fv := notMem_FM_fv htgg

theorem hmvenvB2 : mvB2 ∉ envB2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLB2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRB2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvB2 : tgB2 ∉ envB2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLB2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRB2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (one-way chain) -/

noncomputable def modeB2 (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fRB2 q) (Term.const 1), dom := domRB2, weight := 1 }

def edgeB2 (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrB2 : SearchGraph (Var 6) :=
  { modes := [modeB2 0, modeB2 1, modeB2 2],
    edges := [edgeB2 0 1, edgeB2 0 0, edgeB2 1 2, edgeB2 1 1, edgeB2 2 2] }

theorem GrB2_modeAt (q : ℕ) (hq : q < 3) : GrB2.modeAt q = some (modeB2 q) := by
  interval_cases q <;> rfl

theorem httB2 : ∀ q, ∀ e ∈ GrB2.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrB2.edges := List.mem_of_mem_filter he
  simp only [GrB2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltB2 : ∀ q, ∀ e ∈ GrB2.edgesFrom q, e.tgt < GrB2.modes.length := by
  intro q e he
  have hmem : e ∈ GrB2.edges := List.mem_of_mem_filter he
  simp only [GrB2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrB2, edgeB2]

theorem hRvB2 : ∀ q m, GrB2.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeB2 q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrB2] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrB2] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrB2] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrB2])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRB2 q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRB2 q) (Term.const 1) (hfRB2 q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRB2 hy

theorem edgeB2_mem : ∀ st tgt, edgeB2 st tgt ∈ GrB2.edges →
    edgeB2 st tgt ∈ GrB2.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeB2]⟩

theorem hfreshB2 : ∀ q m, GrB2.modeAt q = some m →
    mvB2 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvB2 q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataB2 : List ((Fin 6 → Term (Var 6)) × Formula (Var 6) × ℕ) :=
  [(fLB2 0, domLB2, 2), (fLB2 1, domLB2, 2), (fLB2 2, domLB2, 2)]

noncomputable def leftProgsB2 (dt : ℝ) : List (Program (Var 6)) :=
  leftDataB2.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgB2 dt d.2.2)

theorem hLB2 : ∀ d ∈ leftDataB2, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataB2, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLB2 0 (by norm_num), hdomLB2⟩
  · exact ⟨hfLB2 1 (by norm_num), hdomLB2⟩
  · exact ⟨hfLB2 2 (by norm_num), hdomLB2⟩

theorem hframesB2 (dt : ℝ) : ∀ P ∈ leftProgsB2 dt, FramesMv P mvB2 := by
  intro P hP
  simp only [leftProgsB2, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgB2 dt d.2.2 mvB2 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hq3n : Run.parseRat "3" = some (3) := by
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
theorem hq1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hqm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hqm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hq06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hqm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hq02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cB2 (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRB20_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 0) x = 3 * (cB2 q - x (Rv 0)) := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cB2]
      try norm_num

theorem fRB21_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 1) x = x (Rv 0) := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRB22_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 2) x = 0 := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem fRB23_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 3) x = 0 := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem fRB24_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 4) x = 0 := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem fRB25_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRB2 q 5) x = 0 := by
  interval_cases q <;>
    · simp [fRB2, hostDyn, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem sat_domRB2 (x : State (Var 6)) : Formula.sat domRB2 x ↔
    (-(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧
      0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/5 ∧
      0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 4) ∧ x (Rv 4) ≤ 11/10) := by
  simp only [domRB2, hostEvolve, mRB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2]
  simp [Run.lowerF, Run.lowerE, hqm05, hq06, hq00, hq08, hqm10, hq11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

/-! ## The invariant's shape and the left-side extractors -/

theorem eval_gB2 (x : State (Var 6)) :
    Term.eval gB2 x = (x (Lv 1) - x (Rv 1) - 1/5) + 1/3 * (x (Lv 0) - x (Rv 0)) := by
  have hdLs : ("L_s".drop 2).copy = "s" := by decide
  have hdRs : ("R_s".drop 2).copy = "s" := by decide
  have hdLv : ("L_v".drop 2).copy = "v" := by decide
  have hdRv : ("R_v".drop 2).copy = "v" := by decide
  simp [gB2, gAt, atomsOf, invB2PF, refinement_ladder_rover_rung2b_6dof_IR, Run.invToG,
    Run.lowerE, vsB2, Run.resolveVar, Parse.dr, hdLs, hdRs, hdLv, hdRv,
    List.findIdx?_cons, hq02, hq1, hq3n, hq0,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]
  try push_cast
  try ring

theorem sat_domLB2 (x : State (Var 6)) : Formula.sat domLB2 x ↔
    (-(1:ℝ)/2 ≤ x (Lv 5) ∧ x (Lv 5) ≤ 3/20 ∧ -(1:ℝ)/2 ≤ x (Lv 2) ∧ x (Lv 2) ≤ 3/20 ∧
      0 ≤ x (Lv 1) ∧ -(1:ℝ)/2 ≤ x (Lv 3) ∧ x (Lv 3) ≤ 3/20 ∧
      0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Lv 4) ∧ x (Lv 4) ≤ 3/20) := by
  simp only [domLB2, hostEvolve, mLB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2]
  simp [Run.lowerF, Run.lowerE, hqm05, hq015, hq00, hq08, hqm10, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  tauto

/-! ## Window facts specialized to the combined coordinate -/

theorem leftBlock_wf (fL : Fin 6 → Term (Var 6)) : (leftBlock fL).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 6)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 6).map hLinj

theorem htg_leftBlock (fL : Fin 6 → Term (Var 6)) : tgB2 ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
  exact aux_ne_Lv 1 i hi

theorem fLB20_eval (l : ℕ) (hl : l < 3) (x : State (Var 6)) :
    Term.eval (fLB2 l 0) x = 3 * (cB2 l - x (Lv 0)) := by
  interval_cases l <;>
    · simp [fLB2, hostDyn, mLB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
        Run.lowerE, hq3n, hq030, hq050, hq065, hq1, hq05, hq03, hqm1, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv, cB2]
      try norm_num

theorem fLB21_eval (l : ℕ) (hl : l < 3) (x : State (Var 6)) :
    Term.eval (fLB2 l 1) x
      = x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 3) * x (Lv 3))) := by
  interval_cases l <;>
    · simp [fLB2, hostDyn, mLB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
        Run.lowerE, hq3n, hq030, hq050, hq065, hq1, hq05, hq03, hqm1, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
      try norm_num
      try ring

/-- The combined coordinate `s + v/3`, as a left-side term. -/
noncomputable def gLwB2 : Term (Var 6) :=
  Term.binop AOp.add (Term.var (Lv 1))
    (Term.binop AOp.mul (Term.const (1/3)) (Term.var (Lv 0)))

theorem window_gL_bound (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (k : ℕ)
    {σ ν : State (Var 6)}
    (hsem : Program.sem (windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt k) σ ν) :
    ν (Lv 1) + 1/3 * ν (Lv 0) ≤ σ (Lv 1) + 1/3 * σ (Lv 0) + 13/20 * ((k : ℝ) * dt) := by
  have hwfL := leftBlock_wf (fLB2 l)
  have htgb := htg_leftBlock (fLB2 l)
  have hbnd : ∀ x : State (Var 6), Formula.sat domLB2 x →
      Lie (DLCalTiming.clk tgB2 (leftBlock (fLB2 l)))
        (fun ω => Term.eval gLwB2 ω) x ≤ 13/20 := by
    intro x hx
    have hfun : (fun ω : State (Var 6) => Term.eval gLwB2 ω)
        = fun y => 1 * y (Lv 1) + (1/3) * y (Lv 0) + 0 := by
      funext y; simp [gLwB2, Term.eval, AOp.interp]
    rw [hfun, lie_two_coord _ (clk_wellFormed tgB2 _ hwfL htgb) (Lv 1) (Lv 0) 1 (1/3) 0 x]
    have hmem1 : ((Lv 1 : Var 6), fLB2 l 1) ∈ DLCalTiming.clk tgB2 (leftBlock (fLB2 l)) := by
      simp only [DLCalTiming.clk, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩)
    have hmem0 : ((Lv 0 : Var 6), fLB2 l 0) ∈ DLCalTiming.clk tgB2 (leftBlock (fLB2 l)) := by
      simp only [DLCalTiming.clk, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
    have hb1 : (Lv 1 : Var 6) ∈ (DLCalTiming.clk tgB2 (leftBlock (fLB2 l))).bound :=
      List.mem_map.mpr ⟨_, hmem1, rfl⟩
    have hb0 : (Lv 0 : Var 6) ∈ (DLCalTiming.clk tgB2 (leftBlock (fLB2 l))).bound :=
      List.mem_map.mpr ⟨_, hmem0, rfl⟩
    have hfield1 : odeField (DLCalTiming.clk tgB2 (leftBlock (fLB2 l))) x (Lv 1)
        = Term.eval (fLB2 l 1) x := by
      simp only [odeField, if_pos hb1]
      rw [ODESystem.rhs_eq_of_mem (clk_wellFormed tgB2 _ hwfL htgb) hmem1]
    have hfield0 : odeField (DLCalTiming.clk tgB2 (leftBlock (fLB2 l))) x (Lv 0)
        = Term.eval (fLB2 l 0) x := by
      simp only [odeField, if_pos hb0]
      rw [ODESystem.rhs_eq_of_mem (clk_wellFormed tgB2 _ hwfL htgb) hmem0]
    rw [hfield1, hfield0, fLB21_eval l hl, fLB20_eval l hl]
    obtain ⟨-, -, -, -, -, -, -, hv0, -, -, -⟩ := (sat_domLB2 x).mp hx
    have hcl : cB2 l ≤ 13/20 := by
      interval_cases l <;> norm_num [cB2]
    nlinarith [mul_nonneg hv0 (mul_self_nonneg (x (Lv 2))),
      mul_nonneg hv0 (mul_self_nonneg (x (Lv 3)))]
  have hg := windowSeg_growth (leftBlock (fLB2 l)) domLB2 tgB2 dt k hwfL htgb
    gLwB2 (13/20) (by norm_num)
    (by intro h
        have h' : tgB2 ∈ Term.fv gLwB2 := h
        simp only [gLwB2, Term.fv, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, false_or, or_false] at h'
        rcases h' with h' | h' <;> exact absurd h' (by simp [tgB2, Lv, Prod.ext_iff]))
    hbnd hdt hsem
  simpa [gLwB2, Term.eval, AOp.interp] using hg

theorem window_maskB2 (l : ℕ) (dt : ℝ) (k : ℕ)
    {σ ν : State (Var 6)}
    (hsem : Program.sem (windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt k) σ ν) :
    ∀ j : Fin 6, ν (Rv j) = σ (Rv j) := by
  intro j
  refine windowSeg_mask (leftBlock (fLB2 l)) domLB2 tgB2 dt k (leftBlock_wf (fLB2 l))
    (htg_leftBlock (fLB2 l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLB2 l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tgB2, Prod.ext_iff])

/-! ## The FLAT hold run — explicit exponential witness -/

/-- The FLAT-mode hold: `v` relaxes exponentially toward `0.65`, `s` integrates
it exactly, `ψ`/`θ` frozen. The combined coordinate `s + v/3` grows at EXACTLY
`0.65` per unit time — the asymptotic `v`-row cancels in the derivative. -/
theorem sem_flat_hold (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 6)}
    (hdom : Formula.sat domRB2 μ) :
    Program.sem (Program.ode (rightBlock (fRB2 2) (Term.const 1)) domRB2) μ
      (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * τ)
        else if x = Rv 1 then
          μ (Rv 1) + 13/20 * τ + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * τ))
        else μ x) := by
  have hR := (sat_domRB2 μ).mp hdom
  have hs0 : (0:ℝ) ≤ μ (Rv 1) := hR.2.2.2.2.1
  have hv0 : (0:ℝ) ≤ μ (Rv 0) := hR.2.2.2.2.2.2.2.1
  have hv8 : μ (Rv 0) ≤ 4/5 := hR.2.2.2.2.2.2.2.2.1
  have hne10 : (Rv 1 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne20 : (Rv 2 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne21 : (Rv 2 : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hne30 : (Rv 3 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne31 : (Rv 3 : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hne40 : (Rv 4 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne41 : (Rv 4 : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  have hne50 : (Rv 5 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne51 : (Rv 5 : Var 6) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
  classical
  refine ⟨τ, fun t x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
      else if x = Rv 1 then
        μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
      else μ x,
    hτ, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0
      simp only [eq_self_iff_true, if_true, if_pos rfl]
      rw [show (-3 : ℝ) * 0 = 0 from by ring, Real.exp_zero]
      ring
    · by_cases h1 : x = Rv 1
      · subst h1
        simp only [if_neg hne10, eq_self_iff_true, if_true]
        rw [show (-3 : ℝ) * 0 = 0 from by ring, Real.exp_zero]
        ring
      · simp [if_neg h0, if_neg h1]
  · rfl
  · intro t ht p hp
    have hexp_d : HasDerivAt (fun u : ℝ => Real.exp (-3 * u))
        (Real.exp (-3 * t) * (-3)) t := by
      have hlin : HasDerivAt (fun u : ℝ => (-3 : ℝ) * u) (-3 : ℝ) t := by
        simpa using (hasDerivAt_id t).const_mul (-3 : ℝ)
      exact hlin.exp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨0, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = (μ (Rv 0) - 13/20) * (Real.exp (-3 * t) * (-3)) := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨0, by norm_num⟩ = fRB2 2 0 from rfl,
          fRB20_eval 2 (by norm_num), cB2]
        try ring
      simp only [heval]
      have h2 : HasDerivWithinAt
          (fun u : ℝ => 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * u))
          ((μ (Rv 0) - 13/20) * (Real.exp (-3 * t) * (-3))) (Set.Icc 0 τ) t :=
        ((hexp_d.const_mul (μ (Rv 0) - 13/20)).const_add (13/20)).hasDerivWithinAt
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp
      · simp
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨1, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t) := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨1, by norm_num⟩ = fRB2 2 1 from rfl,
          fRB21_eval 2 (by norm_num)]
      simp only [heval]
      have hA : HasDerivAt (fun u : ℝ => (13:ℝ)/20 * u) ((13:ℝ)/20) t := by
        simpa using (hasDerivAt_id t).const_mul ((13:ℝ)/20)
      have hAc : HasDerivAt (fun u : ℝ => μ (Rv 1) + 13/20 * u) ((13:ℝ)/20) t :=
        hA.const_add (μ (Rv 1))
      have hB : HasDerivAt (fun u : ℝ => 1 - Real.exp (-3 * u))
          (0 - Real.exp (-3 * t) * (-3)) t :=
        (hasDerivAt_const t (1:ℝ)).sub hexp_d
      have hC : HasDerivAt
          (fun u : ℝ => (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * u)))
          ((μ (Rv 0) - 13/20)/3 * (0 - Real.exp (-3 * t) * (-3))) t :=
        hB.const_mul ((μ (Rv 0) - 13/20)/3)
      have hD := hAc.add hC
      rw [show (13:ℝ)/20 + (μ (Rv 0) - 13/20)/3 * (0 - Real.exp (-3 * t) * (-3))
          = 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t) from by ring] at hD
      refine HasDerivWithinAt.congr hD.hasDerivWithinAt ?_ ?_
      · intro y _; simp [if_neg hne10]
      · simp [if_neg hne10]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨2, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨2, by norm_num⟩ = fRB2 2 2 from rfl,
          fRB22_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 2))) ?_ ?_
      · intro y _; simp [if_neg hne20, if_neg hne21]
      · simp [if_neg hne20, if_neg hne21]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨3, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨3, by norm_num⟩ = fRB2 2 3 from rfl,
          fRB23_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 3))) ?_ ?_
      · intro y _; simp [if_neg hne30, if_neg hne31]
      · simp [if_neg hne30, if_neg hne31]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨4, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨4, by norm_num⟩ = fRB2 2 4 from rfl,
          fRB24_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 4))) ?_ ?_
      · intro y _; simp [if_neg hne40, if_neg hne41]
      · simp [if_neg hne40, if_neg hne41]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRB2 2 ⟨5, by norm_num⟩))
          (fun x => if x = Rv 0 then 13/20 + (μ (Rv 0) - 13/20) * Real.exp (-3 * t)
            else if x = Rv 1 then
              μ (Rv 1) + 13/20 * t + (μ (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * t))
            else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRB2 2 ⟨5, by norm_num⟩ = fRB2 2 5 from rfl,
          fRB25_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 5))) ?_ ?_
      · intro y _; simp [if_neg hne50, if_neg hne51]
      · simp [if_neg hne50, if_neg hne51]
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
    have ht0 : (0:ℝ) ≤ t := ht.1
    have hepos : 0 < Real.exp (-3 * t) := Real.exp_pos _
    have hele1 : Real.exp (-3 * t) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show (-3 : ℝ) * t ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have hle3t : 1 - Real.exp (-3 * t) ≤ 3 * t := by
      have h := Real.add_one_le_exp (-3 * t)
      linarith
    rw [sat_domRB2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [if_neg hne50, if_neg hne51]
      exact hR.1
    · simp only [if_neg hne50, if_neg hne51]
      exact hR.2.1
    · simp only [if_neg hne20, if_neg hne21]
      exact hR.2.2.1
    · simp only [if_neg hne20, if_neg hne21]
      exact hR.2.2.2.1
    · simp only [if_neg hne10, eq_self_iff_true, if_true]
      have hprod : 0 ≤ μ (Rv 0) * (1 - Real.exp (-3 * t)) :=
        mul_nonneg hv0 (by linarith)
      nlinarith
    · simp only [if_neg hne30, if_neg hne31]
      exact hR.2.2.2.2.2.1
    · simp only [if_neg hne30, if_neg hne31]
      exact hR.2.2.2.2.2.2.1
    · simp only [eq_self_iff_true, if_true, if_pos rfl]
      have hprod2 : 0 ≤ μ (Rv 0) * Real.exp (-3 * t) :=
        mul_nonneg hv0 (le_of_lt hepos)
      nlinarith
    · simp only [eq_self_iff_true, if_true, if_pos rfl]
      have hprod3 : 0 ≤ (4/5 - μ (Rv 0)) * Real.exp (-3 * t) :=
        mul_nonneg (by linarith) (le_of_lt hepos)
      nlinarith
    · simp only [if_neg hne40, if_neg hne41]
      exact hR.2.2.2.2.2.2.2.2.2.1
    · simp only [if_neg hne40, if_neg hne41]
      exact hR.2.2.2.2.2.2.2.2.2.2

/-! ## The catch-up step provider — hops to FLAT, one hold run, endpoint arithmetic -/

theorem HmultiB2 (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ P ∈ leftProgsB2 dt, ∀ (q : ℕ), q < GrB2.modes.length → ∀ σ, σ mvB2 = (q : ℝ) →
      Formula.sat (Formula.and (FM gB2 gsB2) envB2) σ →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, GrB2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrB2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gB2 gsB2) envB2)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrB2] using hq
  have hφ : (σ (Lv 1) - σ (Rv 1) - 1/5) + 1/3 * (σ (Lv 0) - σ (Rv 0)) ≤ 0 := by
    have := (sat_FM_iff gB2 gsB2 σ).mp hσ.1 gB2 List.mem_cons_self
    rw [eval_gB2] at this
    linarith
  have hdomRσ : Formula.sat domRB2 σ := hσ.2.2
  simp only [leftProgsB2, leftDataB2, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  -- the response is mode-path-to-FLAT (zero-duration) plus one FLAT hold of 2·dt
  have hchain2 : ∀ (a b c : ℕ × RMode (Var 6) × REdge (Var 6)),
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
  have hbuild : ∀ (l : ℕ), l < 3 → P = windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt 2 →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, GrB2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrB2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gB2 gsB2) envB2)) σ := by
    intro l hl hPeq
    subst hPeq
    -- the faModal body, shared by all starts: the right survives the window,
    -- hops (zero-duration) to FLAT, holds for 2·dt
    have hbody : ∀ (pres : List (Program (Var 6))),
        (∀ Q ∈ pres, ∀ μ : State (Var 6), Formula.sat domRB2 μ →
          Program.sem Q μ μ) →
        Formula.sat (faModal (Equiv.refl (Var 6))
          (windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt 2)
          (bigSeq (pres ++ [Program.ode (rightBlock (fRB2 2) (Term.const 1)) domRB2]))
          (Formula.and (FM gB2 gsB2) envB2)) σ := by
      intro pres hpres
      rw [faModal_sat]
      intro ν hleft
      have hg2 := window_gL_bound l hl dt hdt 2 hleft
      push_cast at hg2
      have hmaskν := window_maskB2 l dt 2 hleft
      have hdomLν := windowSeg_end_domL (leftBlock (fLB2 l)) domLB2 tgB2 dt 2
        (by norm_num) hleft
      have hdomRν : Formula.sat domRB2 ν := by
        rw [sat_domRB2]
        rw [hmaskν 0, hmaskν 1, hmaskν 2, hmaskν 3, hmaskν 4, hmaskν 5]
        exact (sat_domRB2 σ).mp hdomRσ
      set τ : ℝ := 2 * dt with hτdef
      have hτ : 0 ≤ τ := by positivity
      have hhold := sem_flat_hold τ hτ hdomRν
      set μfin : State (Var 6) :=
        (fun x => if x = Rv 0 then 13/20 + (ν (Rv 0) - 13/20) * Real.exp (-3 * τ)
          else if x = Rv 1 then
            ν (Rv 1) + 13/20 * τ + (ν (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * τ))
          else ν x) with hμfin
      -- glue: pres are identity runs on ν, then the hold
      have hsemseq : Program.sem
          (bigSeq (pres ++ [Program.ode (rightBlock (fRB2 2) (Term.const 1)) domRB2]))
          ν μfin := by
        clear hg2
        induction pres with
        | nil =>
            simp only [List.nil_append, bigSeq]
            exact ⟨μfin, hhold, by rw [sem_test]; exact ⟨rfl, trivial⟩⟩
        | cons Q rest ih =>
            simp only [List.cons_append, bigSeq]
            refine ⟨ν, hpres Q List.mem_cons_self ν hdomRν, ?_⟩
            exact ih (fun Q' hQ' => hpres Q' (List.mem_cons_of_mem _ hQ'))
      have hne10 : (Rv 1 : Var 6) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
      have hL1 : μfin (Lv 1) = ν (Lv 1) := by
        simp [hμfin,
          if_neg (show (Lv 1 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
          if_neg (show (Lv 1 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
      have hL0 : μfin (Lv 0) = ν (Lv 0) := by
        simp [hμfin,
          if_neg (show (Lv 0 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
          if_neg (show (Lv 0 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
      have hR0 : μfin (Rv 0) = 13/20 + (ν (Rv 0) - 13/20) * Real.exp (-3 * τ) := by
        simp [hμfin]
      have hR1 : μfin (Rv 1)
          = ν (Rv 1) + 13/20 * τ + (ν (Rv 0) - 13/20)/3 * (1 - Real.exp (-3 * τ)) := by
        simp [hμfin, if_neg hne10]
      have hkey : μfin (Rv 1) + 1/3 * μfin (Rv 0)
          = ν (Rv 1) + 1/3 * ν (Rv 0) + 13/20 * τ := by
        rw [hR0, hR1]; ring
      refine ⟨μfin, by rw [Program.rename_refl]; exact hsemseq, ?_, ?_⟩
      · -- the invariant at the endpoint: catch-up arithmetic
        rw [sat_FM_iff]
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · rw [eval_gB2]
          have hm0 : ν (Rv 0) = σ (Rv 0) := hmaskν 0
          have hm1 : ν (Rv 1) = σ (Rv 1) := hmaskν 1
          have hτeq : τ = 2 * dt := hτdef
          rw [hL1, hL0]
          linarith [hkey, hg2, hφ, hm0, hm1]
        · exact absurd hg' (by simp [gsB2])
      · -- the environment at the endpoint
        constructor
        · -- domL: μfin agrees with ν on left coords
          have : Formula.sat domLB2 μfin := by
            rw [sat_domLB2]
            have h2 : μfin (Lv 2) = ν (Lv 2) := by
              simp [hμfin,
                if_neg (show (Lv 2 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 2 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h3 : μfin (Lv 3) = ν (Lv 3) := by
              simp [hμfin,
                if_neg (show (Lv 3 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 3 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h4 : μfin (Lv 4) = ν (Lv 4) := by
              simp [hμfin,
                if_neg (show (Lv 4 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 4 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            have h5 : μfin (Lv 5) = ν (Lv 5) := by
              simp [hμfin,
                if_neg (show (Lv 5 : Var 6) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
                if_neg (show (Lv 5 : Var 6) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
            rw [hL1, hL0, h2, h3, h4, h5]
            exact (sat_domLB2 ν).mp hdomLν
          exact this
        · exact sem_ode_ends_in_domain hhold
    -- dispatch on the start mode: zero-hops up the chain, hold in FLAT
    interval_cases q
    · refine ⟨[(0, modeB2 0, edgeB2 0 1), (1, modeB2 1, edgeB2 1 2), (2, modeB2 2, edgeB2 2 2)],
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrB2_modeAt 0 (by norm_num), edgeB2_mem 0 1 (by simp [GrB2])⟩
        · exact ⟨GrB2_modeAt 1 (by norm_num), edgeB2_mem 1 2 (by simp [GrB2])⟩
        · exact ⟨GrB2_modeAt 2 (by norm_num), edgeB2_mem 2 2 (by simp [GrB2])⟩
      · exact hchain2 _ _ _ rfl rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRB2 0) (Term.const 1)) domRB2,
          Program.ode (rightBlock (fRB2 1) (Term.const 1)) domRB2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRB2 0)
                (lam := Term.const 1) (domR := domRB2) hdom
              rwa [hρ] at hsem
            · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRB2 1)
                (lam := Term.const 1) (domR := domRB2) hdom
              rwa [hρ] at hsem)
        simpa [modeB2] using this
    · refine ⟨[(1, modeB2 1, edgeB2 1 2), (2, modeB2 2, edgeB2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrB2_modeAt 1 (by norm_num), edgeB2_mem 1 2 (by simp [GrB2])⟩
        · exact ⟨GrB2_modeAt 2 (by norm_num), edgeB2_mem 2 2 (by simp [GrB2])⟩
      · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
        intro y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; rfl
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [Program.ode (rightBlock (fRB2 1) (Term.const 1)) domRB2]
          (by
            intro Q hQ μ hdom
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            subst hQ
            obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRB2 1)
              (lam := Term.const 1) (domR := domRB2) hdom
            rwa [hρ] at hsem)
        simpa [modeB2] using this
    · refine ⟨[(2, modeB2 2, edgeB2 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl
        exact ⟨GrB2_modeAt 2 (by norm_num), edgeB2_mem 2 2 (by simp [GrB2])⟩
      · simp
      · intro s hs
        simp only [List.head?_cons, Option.some_inj] at hs
        rw [← hs]
      · have := hbody [] (by intro Q hQ; exact absurd hQ (List.not_mem_nil))
        simpa [modeB2] using this
  rcases hP with rfl | rfl | rfl
  · exact hbuild 0 (by norm_num) rfl
  · exact hbuild 1 (by norm_num) rfl
  · exact hbuild 2 (by norm_num) rfl

/-- **`refinement_ladder_rover_rung2b_6dof`, modal Theorem 3** — the COMBINED-
COORDINATE catch-up form: the declared tolerance bounds `g₂ = s + v/3`, whose
Lie along the right's FLAT hold is EXACTLY `0.65` (the asymptotic `v`-row
cancels), matching the left window's `windowSeg_growth` ceiling `0.65·(2·dt)`.
A hold of `τ = 2·dt` on an explicit exponential witness re-establishes the
invariant with zero slack. Z3-free: NO verdict hypotheses at all. -/
theorem rung2b_6dof_modal (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsB2 dt))
      (rightAutomatonBody GrB2 mvB2)
      (RFormula.and (RFormula.and (canonInvM gB2 gsB2) (envLR domLB2 domRB2))
        (mvValidR mvB2 GrB2.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrB2 mvB2 (FM gB2 gsB2) domLB2 domRB2
    (leftProgsB2 dt) (canonInvM gB2 gsB2) (encode_canonInvM gB2 gsB2) ?_ ?_ ?_
  · exact hdis_multi GrB2 0 1 dt leftDataB2 (by decide) httB2 hRvB2 hLB2
  · exact hstep_assembled_multiF GrB2 mvB2 (FM gB2 gsB2) envB2 (leftProgsB2 dt)
      hmvFB2 hmvenvB2 hfreshB2 httB2 hltB2 (hframesB2 dt)
      (HmultiB2 dt hdt)
  · exact hddF_multiE GrB2 0 1 dt leftDataB2 (canonInvM gB2 gsB2) domLB2 domRB2
      (by decide) httB2 hRvB2 hLB2
      (canonInvM_varsL gB2 gsB2 (by
        intro g' hg'
        simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gB2 gsB2) hdomLB2 hdomRB2

end RoverRung2b6dofModal
end RelCertifier
