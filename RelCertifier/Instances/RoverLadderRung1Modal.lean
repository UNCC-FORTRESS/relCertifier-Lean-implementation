/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `refinement_ladder_rover_rung1_2to3`, modal Theorem 3 (multi-component pilot)

The first PLAIN list-invariant instance (the multiF chain without rung2c's region
device): the 3-DOF terrain rover (nonlinear left `s' = v(1 − ψ²/2)`) refines the
2-DOF kinematic chain at the two-component tolerance `v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`,
three same-band windows at λ = 1, k = 1.

The right graph is the one-way chain `STEEP → MODER → FLAT`, but unlike rung2c no
pair is vacuous: the cover certifies the joint coupling for every (window, start)
at or ahead of the window (all three for the `STEEP` window), and behind-the-window
starts CLIMB — static hops up the chain, then the certified coupling at the reached
mode. Existence is the `match_multi_eps` face shape one dimension up: strict `v`
faces, the non-strict `s ≥ 0` face conditioned on the core, affine fields
(`K = 3`, `L = 8`), Z3-free.

Residuals: six stratified-DC verdict packs (`VerdE l m` — the certified
(window, mode) couplings, two queries each). Axioms: the standard three +
`z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung1_2to3

namespace RelCertifier
namespace RoverLadderRung1Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsE : List String := ["v", "s", "psi"]
def dummyE : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLE (l : ℕ) : Parse.PMode :=
  refinement_ladder_rover_rung1_2to3_IR.L.modes.getD l dummyE
def mRE (q : ℕ) : Parse.PMode :=
  refinement_ladder_rover_rung1_2to3_IR.R.modes.getD q dummyE

abbrev mvE : Var 3 := (Side.Aux, 0)
abbrev aE : Fin 3 := (1 : Fin 3)
abbrev tgE : Var 3 := (Side.Aux, aE)

noncomputable def fLE (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsE 3 Side.L (mLE l)
noncomputable def fRE (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsE 3 Side.R (mRE q)
noncomputable def domLE : Formula (Var 3) := hostEvolve vsE 3 Side.L (mLE 0)
noncomputable def domRE : Formula (Var 3) := hostEvolve vsE 3 Side.R (mRE 0)
noncomputable def envE : Formula (Var 3) := Formula.and domLE domRE

/-! ## The two-component invariant -/

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invEPF : Parse.PForm :=
  (refinement_ladder_rover_rung1_2to3_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 3) :=
  ((Run.invToG vsE 3 ((atomsOf invEPF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gE : Term (Var 3) := gAt 0
noncomputable def gsE : List (Term (Var 3)) := [gAt 1]

/-! ## Side-splits -/

theorem fLE_pipe (l : ℕ) (i : Fin 3) : fLE l i =
    (((some (mLE l)).bind (Run.dynOf vsE 3 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRE_pipe (q : ℕ) (i : Fin 3) : fRE q i =
    (((some (mRE q)).bind (Run.dynOf vsE 3 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLE_pipe : domLE =
    (((some (mLE 0)).bind (fun m => Run.lowerF vsE 3 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRE_pipe : domRE =
    (((some (mRE 0)).bind (fun m => Run.lowerF vsE 3 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLE (l : ℕ) (hl : l < 3) : ∀ i, (fLE l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsE) (some (mLE l))
    (by interval_cases l <;>
      simp [mLE, refinement_ladder_rover_rung1_2to3_IR, Parse.PExpr.namesFree]) i x
    (fLE_pipe l i ▸ hx))

theorem hfRE (q : ℕ) (hq : q < 3) : ∀ i, (fRE q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsE) (some (mRE q))
    (by interval_cases q <;>
      simp [mRE, refinement_ladder_rover_rung1_2to3_IR, Parse.PExpr.namesFree]) i x
    (fRE_pipe q i ▸ hx))

theorem hdomLE : domLE.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsE) (some (mLE 0))
    (by simp [mLE, refinement_ladder_rover_rung1_2to3_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLE_pipe ▸ hx))

theorem hdomRE : domRE.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsE) (some (mRE 0))
    (by simp [mRE, refinement_ladder_rover_rung1_2to3_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRE_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gE :: gsE, mvE ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gE :: gsE, tgE ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFE : mvE ∉ (FM gE gsE).fv := notMem_FM_fv hmvg
theorem htgFE : tgE ∉ (FM gE gsE).fv := notMem_FM_fv htgg

theorem hmvenvE : mvE ∉ envE.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLE h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRE h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvE : tgE ∉ envE.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLE h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRE h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (one-way chain) -/

noncomputable def modeE (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRE q) (Term.const 1), dom := domRE, weight := 1 }

def edgeE (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrE : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeE 0 1, edgeE 0 0, edgeE 1 2, edgeE 1 1, edgeE 2 2] }

theorem GrE_modeAt (q : ℕ) (hq : q < 3) : GrE.modeAt q = some (modeE q) := by
  interval_cases q <;> rfl

theorem httE : ∀ q, ∀ e ∈ GrE.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrE.edges := List.mem_of_mem_filter he
  simp only [GrE, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltE : ∀ q, ∀ e ∈ GrE.edgesFrom q, e.tgt < GrE.modes.length := by
  intro q e he
  have hmem : e ∈ GrE.edges := List.mem_of_mem_filter he
  simp only [GrE, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrE, edgeE]

theorem hRvE : ∀ q m, GrE.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeE q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrE] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrE] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrE] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrE])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRE q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRE q) (Term.const 1) (hfRE q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRE hy

theorem edgeE_mem : ∀ st tgt, edgeE st tgt ∈ GrE.edges →
    edgeE st tgt ∈ GrE.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeE]⟩

theorem hfreshE : ∀ q m, GrE.modeAt q = some m →
    mvE ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvE q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family (three windows, λ = 1, k = 1) -/

noncomputable def leftDataE : List ((Fin 3 → Term (Var 3)) × Formula (Var 3) × ℕ) :=
  [(fLE 0, domLE, 1), (fLE 1, domLE, 1), (fLE 2, domLE, 1)]

noncomputable def leftProgsE (dt : ℝ) : List (Program (Var 3)) :=
  leftDataE.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgE dt d.2.2)

theorem hLE : ∀ d ∈ leftDataE, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataE, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLE 0 (by norm_num), hdomLE⟩
  · exact ⟨hfLE 1 (by norm_num), hdomLE⟩
  · exact ⟨hfLE 2 (by norm_num), hdomLE⟩

theorem hframesE (dt : ℝ) : ∀ P ∈ leftProgsE dt, FramesMv P mvE := by
  intro P hP
  simp only [leftProgsE, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgE dt d.2.2 mvE (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem he030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem he00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem he08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstE (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRE0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 0) x = 3 * (cstE q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstE]

theorem fRE1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRE2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 2) x = 0 := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRE (x : State (Var 3)) : Formula.sat domRE x ↔
    (0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5) := by
  simp only [domRE, hostEvolve, mRE, refinement_ladder_rover_rung1_2to3_IR, vsE]
  simp [Run.lowerF, Run.lowerE, he00, he08, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

theorem gAt0_eval (x : State (Var 3)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invEPF, refinement_ladder_rover_rung1_2to3_IR, Run.invToG,
    Run.lowerE, vsE, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 3)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invEPF, refinement_ladder_rover_rung1_2to3_IR, Run.invToG,
    Run.lowerE, vsE, he02, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-! ## Existence (match_multi_eps shape, one dimension up) -/

noncomputable def faceVLo : Term (Var 3) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 3) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))
noncomputable def faceSLo : Term (Var 3) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))

theorem faces_fv_RE : ∀ gT ∈ [faceVLo, faceVHi, faceSLo], ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, faceSLo, Term.fv, Set.mem_union,
        Set.mem_empty_iff_false, false_or, or_false, Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

theorem odeField_RE (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    odeField (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cstE q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have h0 : (Lv j : Var 3) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      have h1 : (Lv j : Var 3) ≠ Rv 1 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, h0, h1]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRE0_eval q hq]
      · have h0 : (Rv (1 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRE1_eval q hq, h0]
      · have h0 : (Rv (2 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        have h1 : (Rv (2 : Fin 3) : Var 3) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRE2_eval q hq, h0, h1]
  · have hnotR : ∀ j : Fin 3, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1)]

theorem hbndS_E (q : ℕ) (hq : q < 3) : ∀ gT ∈ [faceVLo, faceVHi], ∀ x : State (Var 3),
    Term.eval gT x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1))
      (fun ω => Term.eval gT ω) x < 0 := by
  intro gT hgT x hface
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl
  · have hx0 : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 3) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
      odeField_RE q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstE]
  · have hx0 : x (Rv 0) = 4/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 3) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-(4/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(4/5)) x,
      odeField_RE q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstE]

theorem hbndN_E (q : ℕ) (hq : q < 3) (x : State (Var 3))
    (hcore : Term.eval faceVLo x ≤ 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1))
      (fun ω => Term.eval faceSLo ω) x ≤ 0 := by
  have hv0 : 0 ≤ x (Rv 0) := by
    simp only [faceVLo, Term.eval, AOp.interp] at hcore; linarith
  have h10 : (Rv (1 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hfun : (fun ω : State (Var 3) => Term.eval faceSLo ω)
      = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
    funext y; simp [faceSLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
    odeField_RE q hq]
  simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl]
  linarith

theorem hLip_E (q : ℕ) (hq : q < 3) (ν : State (Var 3)) :
    LipschitzOnWith 3 (odeField (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RE q hq, odeField_RE q hq]
  have hdc : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
    have h := dist_le_pi_dist x y (Rv 0)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  have hcoe : ((3 : NNReal) : ℝ) = 3 := rfl
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : 3 * (cstE q - x (Rv 0)) - 3 * (cstE q - y (Rv 0))
        = -3 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have habs : |(-3 : ℝ)| = 3 := by norm_num
    rw [habs, hcoe]
    nlinarith
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    nlinarith [hdc, abs_nonneg (x (Rv 0) - y (Rv 0))]
  · simp only [if_neg hc0, if_neg hc1]
    rw [hcoe]
    simp [dist_nonneg]

theorem hfbnd_E (q : ℕ) (hq : q < 3) (ν : State (Var 3))
    (hν : ∀ gT ∈ [faceVLo, faceVHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  intro x hx
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp)
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν8 : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp)
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at this
    linarith
  have hxb : |x (Rv 0)| ≤ 9/5 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν8⟩
    linarith [abs_le.mp hνb]
  rw [odeField_RE q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cstE q ∧ cstE q ≤ 13/20 := by
      interval_cases q <;> norm_num [cstE]
    rw [abs_le]
    push_cast
    obtain ⟨hc1, hc2⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hxb]
  by_cases hc1 : c = Rv 1
  · subst hc1
    have h10 : (Rv (1 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
    simp only [if_neg h10, eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    push_cast
    linarith [abs_le.mp hxb]
  · simp only [if_neg hc0, if_neg hc1]
    norm_num

theorem esE (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM gE gsE) envE) σ →
      HExistSegB (fLE l) (fRE m) (Term.const 1) domLE domRE dt
        (Function.update σ tgE 0) := by
  intro σ hσ
  have hR : Formula.sat domRE σ := hσ.2.2
  rw [sat_domRE] at hR
  obtain ⟨hs0, hv0, hv8⟩ := hR
  have hupd : ∀ j : Fin 3, σ (Side.R, j) = Function.update σ tgE 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgE, Prod.ext_iff])]
  have hfS : ∀ gT ∈ [faceVLo, faceVHi],
      Term.eval gT (Function.update σ tgE 0) ≤ 0 := by
    intro gT hgT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl
    · simp only [faceVLo, Term.eval, AOp.interp, Rv]
      rw [← hupd]; linarith
    · simp only [faceVHi, Term.eval, AOp.interp, Rv]
      rw [← hupd]; linarith
  have hfN : ∀ gT ∈ [faceSLo],
      Term.eval gT (Function.update σ tgE 0) ≤ 0 := by
    intro gT hgT
    rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceSLo, Term.eval, AOp.interp, Rv]
    rw [← hupd]; linarith
  refine HExistSegB_of_viability_stratified (fLE l) (fRE m) (Term.const 1)
    domLE domRE [faceVLo, faceVHi] [] [faceSLo] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLE l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RE gT (by
        rcases List.mem_append.mp hgT with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self
          · rw [List.mem_singleton] at h; subst h; simp
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x hx hb
      rw [List.mem_singleton] at hgT
      subst hgT
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLE l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RE faceSLo (by simp) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x _ hface
      exact hbndS_E m hm gT hgT x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      exact hbndN_E m hm x (hx faceVLo (List.mem_append_left _ List.mem_cons_self)))
    (by
      intro x hS hN
      have h0 : 0 ≤ x (Rv 0) := by
        have := hS faceVLo (List.mem_append_left _ List.mem_cons_self)
        simp only [faceVLo, Term.eval, AOp.interp] at this
        linarith
      have hv : x (Rv 0) ≤ 4/5 := by
        have := hS faceVHi (List.mem_append_left _ (by simp))
        simp only [faceVHi, Term.eval, AOp.interp] at this
        linarith
      have hs : 0 ≤ x (Rv 1) := by
        have := hN faceSLo List.mem_cons_self
        simp only [faceSLo, Term.eval, AOp.interp] at this
        linarith
      exact (sat_domRE x).mpr ⟨hs, h0, hv⟩)
    3 8 1 one_pos
    (fun ν0 _ => hLip_E m hm ν0)
    (fun ν0 h0 => hfbnd_E m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgE 0)
    hfS
    hfN
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

end RoverLadderRung1Modal
end RelCertifier