/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `rover_dof_terrain_rung3`, modal Theorem 3 (multiF at n = 12)

The terrain multiF pattern at twelve coordinates (GENERATED from the n = 8
block templates): five decaying right rows, six zero-field rows, same one-way
chain and climb dispatch, existence Z3-free (`K = 3`, `L = 8`). Residuals:
six stratified-DC packs (`VerdW l m`). Axioms: the standard three +
`z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3

namespace RelCertifier
namespace RoverDofTerrainRung3Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 3200000

def vsW : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
def dummyW : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLW (l : ℕ) : Parse.PMode := rover_dof_terrain_rung3_IR.L.modes.getD l dummyW
def mRW (q : ℕ) : Parse.PMode := rover_dof_terrain_rung3_IR.R.modes.getD q dummyW

abbrev mvW : Var 12 := (Side.Aux, 0)
abbrev aW : Fin 12 := (1 : Fin 12)
abbrev tgW : Var 12 := (Side.Aux, aW)

noncomputable def fLW (l : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsW 12 Side.L (mLW l)
noncomputable def fRW (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsW 12 Side.R (mRW q)
noncomputable def domLW : Formula (Var 12) := hostEvolve vsW 12 Side.L (mLW 0)
noncomputable def domRW : Formula (Var 12) := hostEvolve vsW 12 Side.R (mRW 0)
noncomputable def envW : Formula (Var 12) := Formula.and domLW domRW

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invWPF : Parse.PForm :=
  (rover_dof_terrain_rung3_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 12) :=
  ((Run.invToG vsW 12 ((atomsOf invWPF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gW : Term (Var 12) := gAt 0
noncomputable def gsW : List (Term (Var 12)) := [gAt 1]

theorem fLW_pipe (l : ℕ) (i : Fin 12) : fLW l i =
    (((some (mLW l)).bind (Run.dynOf vsW 12 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRW_pipe (q : ℕ) (i : Fin 12) : fRW q i =
    (((some (mRW q)).bind (Run.dynOf vsW 12 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLW_pipe : domLW =
    (((some (mLW 0)).bind (fun m => Run.lowerF vsW 12 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRW_pipe : domRW =
    (((some (mRW 0)).bind (fun m => Run.lowerF vsW 12 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLW (l : ℕ) (hl : l < 3) : ∀ i, (fLW l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsW) (some (mLW l))
    (by interval_cases l <;>
      simp [mLW, rover_dof_terrain_rung3_IR, Parse.PExpr.namesFree]) i x
    (fLW_pipe l i ▸ hx))

theorem hfRW (q : ℕ) (hq : q < 3) : ∀ i, (fRW q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsW) (some (mRW q))
    (by interval_cases q <;>
      simp [mRW, rover_dof_terrain_rung3_IR, Parse.PExpr.namesFree]) i x
    (fRW_pipe q i ▸ hx))

theorem hdomLW : domLW.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsW) (some (mLW 0))
    (by simp [mLW, rover_dof_terrain_rung3_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLW_pipe ▸ hx))

theorem hdomRW : domRW.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsW) (some (mRW 0))
    (by simp [mRW, rover_dof_terrain_rung3_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRW_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gW :: gsW, mvW ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gW, gsW, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gW :: gsW, tgW ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gW, gsW, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFW : mvW ∉ (FM gW gsW).fv := notMem_FM_fv hmvg
theorem htgFW : tgW ∉ (FM gW gsW).fv := notMem_FM_fv htgg

theorem hmvenvW : mvW ∉ envW.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvW : tgW ∉ envW.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

noncomputable def modeW (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRW q) (Term.const 1), dom := domRW, weight := 1 }

def edgeW (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrW : SearchGraph (Var 12) :=
  { modes := [modeW 0, modeW 1, modeW 2],
    edges := [edgeW 0 1, edgeW 0 0, edgeW 1 2, edgeW 1 1, edgeW 2 2] }

theorem GrW_modeAt (q : ℕ) (hq : q < 3) : GrW.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem httW : ∀ q, ∀ e ∈ GrW.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrW.edges := List.mem_of_mem_filter he
  simp only [GrW, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltW : ∀ q, ∀ e ∈ GrW.edgesFrom q, e.tgt < GrW.modes.length := by
  intro q e he
  have hmem : e ∈ GrW.edges := List.mem_of_mem_filter he
  simp only [GrW, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrW, edgeW]

theorem hRvW : ∀ q m, GrW.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeW q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrW])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRW q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRW q) (Term.const 1) (hfRW q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRW hy

theorem edgeW_mem : ∀ st tgt, edgeW st tgt ∈ GrW.edges →
    edgeW st tgt ∈ GrW.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeW]⟩

theorem hfreshW : ∀ q m, GrW.modeAt q = some m →
    mvW ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvW q m hm (vars_ode_sub _ _ (Or.inl hmv)))

noncomputable def leftDataW : List ((Fin 12 → Term (Var 12)) × Formula (Var 12) × ℕ) :=
  [(fLW 0, domLW, 1), (fLW 1, domLW, 1), (fLW 2, domLW, 1)]

noncomputable def leftProgsW (dt : ℝ) : List (Program (Var 12)) :=
  leftDataW.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgW dt d.2.2)

theorem hLW : ∀ d ∈ leftDataW, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataW, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLW 0 (by norm_num), hdomLW⟩
  · exact ⟨hfLW 1 (by norm_num), hdomLW⟩
  · exact ⟨hfLW 2 (by norm_num), hdomLW⟩

theorem hframesW (dt : ℝ) : ∀ P ∈ leftProgsW dt, FramesMv P mvW := by
  intro P hP
  simp only [leftProgsW, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgW dt d.2.2 mvW (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

theorem hw030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hw050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hw065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hw3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hwm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hw0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hw00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hw08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hw02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hwm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hw015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hwm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hw11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

noncomputable def cstW (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20


theorem fRW0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 0) x = 3 * (cstW q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstW]

theorem fRW1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 3) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 5) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 7) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 9) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 10) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 11) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IR, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRW (x : State (Var 12)) : Formula.sat domRW x ↔
    (-(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 7) ∧ x (Rv 7) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ (11:ℝ)/10 ∧ -(1:ℝ)/2 ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 9) ∧ x (Rv 9) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20) := by
  simp only [domRW, hostEvolve, mRW, rover_dof_terrain_rung3_IR, vsW]
  simp [Run.lowerF, Run.lowerE, hwm05, hw015, hw00, hw08, hwm10, hw11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

theorem gAt0_eval (x : State (Var 12)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invWPF, rover_dof_terrain_rung3_IR, Run.invToG,
    Run.lowerE, vsW, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 12)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invWPF, rover_dof_terrain_rung3_IR, Run.invToG,
    Run.lowerE, vsW, hw02, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

noncomputable def faceVLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (0)) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))

noncomputable def facePsiLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 2))
noncomputable def facePsiHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 2)) (Term.const ((3:ℝ)/20))

noncomputable def faceThLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 4))
noncomputable def faceThHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 4)) (Term.const ((3:ℝ)/20))

noncomputable def facePhLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 6))
noncomputable def facePhHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 6)) (Term.const ((3:ℝ)/20))

noncomputable def faceZLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 8))
noncomputable def faceZHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 8)) (Term.const ((3:ℝ)/20))

noncomputable def faceSLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))

noncomputable def faceOPsLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 3))
noncomputable def faceOPsHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 3)) (Term.const ((11:ℝ)/10))

noncomputable def faceOThLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 5))
noncomputable def faceOThHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 5)) (Term.const ((11:ℝ)/10))

noncomputable def faceOPhLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 7))
noncomputable def faceOPhHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 7)) (Term.const ((11:ℝ)/10))

noncomputable def faceVzLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 9))
noncomputable def faceVzHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 9)) (Term.const ((11:ℝ)/10))

noncomputable def faceAxLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 10))
noncomputable def faceAxHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 10)) (Term.const ((11:ℝ)/10))

noncomputable def faceAyLo : Term (Var 12) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 11))
noncomputable def faceAyHi : Term (Var 12) :=
  Term.binop AOp.sub (Term.var (Rv 11)) (Term.const ((11:ℝ)/10))

noncomputable def gsSW : List (Term (Var 12)) :=
  [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi, facePhLo, facePhHi, faceZLo, faceZHi]
noncomputable def gsNW : List (Term (Var 12)) :=
  [faceSLo, faceOPsLo, faceOPsHi, faceOThLo, faceOThHi, faceOPhLo, faceOPhHi, faceVzLo, faceVzHi, faceAxLo, faceAxHi, faceAyLo, faceAyHi]

theorem faces_fv_RW : ∀ gT' ∈ gsSW ++ gsNW, ∀ x ∈ gT'.fv, x ∈ range Rv := by
  intro gT' hgT x hx
  simp only [gsSW, gsNW, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi, facePhLo, facePhHi, faceZLo, faceZHi, faceSLo, faceOPsLo, faceOPsHi, faceOThLo, faceOThHi, faceOPhLo, faceOPhHi, faceVzLo, faceVzHi, faceAxLo, faceAxHi, faceAyLo, faceAyHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false,
        false_or, or_false, Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

theorem odeField_RW (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    odeField (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cstW q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0)
        else if c = Rv 2 then -1 * x (Rv 2)
        else if c = Rv 4 then -1 * x (Rv 4)
        else if c = Rv 6 then -1 * x (Rv 6)
        else if c = Rv 8 then -1 * x (Rv 8)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
      intro a b hab
      simp [Rv, Prod.ext_iff]
      exact fun h => hab (by exact_mod_cast h)
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have hLR : ∀ k : Fin 12, (Lv j : Var 12) ≠ Rv k := by
        intro k
        simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, hLR 0, hLR 1, hLR 2, hLR 4, hLR 6, hLR 8]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRW0_eval q hq]
      · simp [Term.eval, AOp.interp, fRW1_eval q hq,
          hne 1 0 (by decide)]
      · simp [Term.eval, AOp.interp, fRW2_eval q hq,
          hne 2 0 (by decide),
          hne 2 1 (by decide)]
      · simp [Term.eval, AOp.interp, fRW3_eval q hq,
          hne 3 0 (by decide),
          hne 3 1 (by decide),
          hne 3 2 (by decide),
          hne 3 4 (by decide),
          hne 3 6 (by decide),
          hne 3 8 (by decide)]
      · simp [Term.eval, AOp.interp, fRW4_eval q hq,
          hne 4 0 (by decide),
          hne 4 1 (by decide),
          hne 4 2 (by decide)]
      · simp [Term.eval, AOp.interp, fRW5_eval q hq,
          hne 5 0 (by decide),
          hne 5 1 (by decide),
          hne 5 2 (by decide),
          hne 5 4 (by decide),
          hne 5 6 (by decide),
          hne 5 8 (by decide)]
      · simp [Term.eval, AOp.interp, fRW6_eval q hq,
          hne 6 0 (by decide),
          hne 6 1 (by decide),
          hne 6 2 (by decide),
          hne 6 4 (by decide)]
      · simp [Term.eval, AOp.interp, fRW7_eval q hq,
          hne 7 0 (by decide),
          hne 7 1 (by decide),
          hne 7 2 (by decide),
          hne 7 4 (by decide),
          hne 7 6 (by decide),
          hne 7 8 (by decide)]
      · simp [Term.eval, AOp.interp, fRW8_eval q hq,
          hne 8 0 (by decide),
          hne 8 1 (by decide),
          hne 8 2 (by decide),
          hne 8 4 (by decide),
          hne 8 6 (by decide)]
      · simp [Term.eval, AOp.interp, fRW9_eval q hq,
          hne 9 0 (by decide),
          hne 9 1 (by decide),
          hne 9 2 (by decide),
          hne 9 4 (by decide),
          hne 9 6 (by decide),
          hne 9 8 (by decide)]
      · simp [Term.eval, AOp.interp, fRW10_eval q hq,
          hne 10 0 (by decide),
          hne 10 1 (by decide),
          hne 10 2 (by decide),
          hne 10 4 (by decide),
          hne 10 6 (by decide),
          hne 10 8 (by decide)]
      · simp [Term.eval, AOp.interp, fRW11_eval q hq,
          hne 11 0 (by decide),
          hne 11 1 (by decide),
          hne 11 2 (by decide),
          hne 11 4 (by decide),
          hne 11 6 (by decide),
          hne 11 8 (by decide)]
  · have hnotR : ∀ j : Fin 12, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1), if_neg (hnotR 2), if_neg (hnotR 4), if_neg (hnotR 6), if_neg (hnotR 8)]

theorem hbndS_W (q : ℕ) (hq : q < 3) : ∀ gT' ∈ gsSW, ∀ x : State (Var 12),
    Term.eval gT' x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1))
      (fun ω => Term.eval gT' ω) x < 0 := by
  have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro gT' hgT x hface
  simp only [gsSW, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hx : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + (0) := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) (0) x,
      odeField_RW q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx]
    interval_cases q <;> norm_num [cstW]
  · have hx : x (Rv 0) = (4:ℝ)/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-((4:ℝ)/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-((4:ℝ)/5)) x,
      odeField_RW q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx]
    interval_cases q <;> norm_num [cstW]
  · have hx : x (Rv 2) = -(1:ℝ)/2 := by
      simp only [facePsiLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval facePsiLo ω)
        = fun y => (-1 : ℝ) * y (Rv 2) + (-(1:ℝ)/2) := by
      funext y; simp [facePsiLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) (-1) (-(1:ℝ)/2) x,
      odeField_RW q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 2) = (3:ℝ)/20 := by
      simp only [facePsiHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval facePsiHi ω)
        = fun y => (1 : ℝ) * y (Rv 2) + (-((3:ℝ)/20)) := by
      funext y; simp [facePsiHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) 1 (-((3:ℝ)/20)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = -(1:ℝ)/2 := by
      simp only [faceThLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 4) + (-(1:ℝ)/2) := by
      funext y; simp [faceThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) (-1) (-(1:ℝ)/2) x,
      odeField_RW q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = (3:ℝ)/20 := by
      simp only [faceThHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceThHi ω)
        = fun y => (1 : ℝ) * y (Rv 4) + (-((3:ℝ)/20)) := by
      funext y; simp [faceThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) 1 (-((3:ℝ)/20)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 6) = -(1:ℝ)/2 := by
      simp only [facePhLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval facePhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 6) + (-(1:ℝ)/2) := by
      funext y; simp [facePhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) (-1) (-(1:ℝ)/2) x,
      odeField_RW q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)), if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 6) = (3:ℝ)/20 := by
      simp only [facePhHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval facePhHi ω)
        = fun y => (1 : ℝ) * y (Rv 6) + (-((3:ℝ)/20)) := by
      funext y; simp [facePhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) 1 (-((3:ℝ)/20)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)), if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 8) = -(1:ℝ) := by
      simp only [faceZLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceZLo ω)
        = fun y => (-1 : ℝ) * y (Rv 8) + (-(1:ℝ)) := by
      funext y; simp [faceZLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 8) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 8 0 (by decide)), if_neg (hne 8 1 (by decide)), if_neg (hne 8 2 (by decide)), if_neg (hne 8 4 (by decide)), if_neg (hne 8 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 8) = (3:ℝ)/20 := by
      simp only [faceZHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 12) => Term.eval faceZHi ω)
        = fun y => (1 : ℝ) * y (Rv 8) + (-((3:ℝ)/20)) := by
      funext y; simp [faceZHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 8) 1 (-((3:ℝ)/20)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 8 0 (by decide)), if_neg (hne 8 1 (by decide)), if_neg (hne 8 2 (by decide)), if_neg (hne 8 4 (by decide)), if_neg (hne 8 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num

theorem hbndN_W (q : ℕ) (hq : q < 3) : ∀ i (hi : i < gsNW.length), ∀ x : State (Var 12),
    (∀ gT' ∈ gsSW ++ ([] : List (Term (Var 12))), Term.eval gT' x ≤ 0) →
    Lie (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1))
      (fun ω => Term.eval gsNW[i] ω) x ≤ 0 := by
  have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro i hi x hx
  have hi13 : i < 13 := by simpa [gsNW] using hi
  have hv0 : 0 ≤ x (Rv 0) := by
    have := hx faceVLo (List.mem_append_left _ (by simp [gsSW]))
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  interval_cases i
  · show Lie _ (fun ω => Term.eval faceSLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceSLo ω)
        = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [faceSLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
      odeField_RW q hq]
    simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    linarith
  · show Lie _ (fun ω => Term.eval faceOPsLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOPsLo ω)
        = fun y => (-1 : ℝ) * y (Rv 3) + (-(1:ℝ)) := by
      funext y; simp [faceOPsLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)), if_neg (hne 3 2 (by decide)), if_neg (hne 3 4 (by decide)), if_neg (hne 3 6 (by decide)), if_neg (hne 3 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOPsHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOPsHi ω)
        = fun y => (1 : ℝ) * y (Rv 3) + (-((11:ℝ)/10)) := by
      funext y; simp [faceOPsHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)), if_neg (hne 3 2 (by decide)), if_neg (hne 3 4 (by decide)), if_neg (hne 3 6 (by decide)), if_neg (hne 3 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOThLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 5) + (-(1:ℝ)) := by
      funext y; simp [faceOThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)), if_neg (hne 5 2 (by decide)), if_neg (hne 5 4 (by decide)), if_neg (hne 5 6 (by decide)), if_neg (hne 5 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOThHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOThHi ω)
        = fun y => (1 : ℝ) * y (Rv 5) + (-((11:ℝ)/10)) := by
      funext y; simp [faceOThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)), if_neg (hne 5 2 (by decide)), if_neg (hne 5 4 (by decide)), if_neg (hne 5 6 (by decide)), if_neg (hne 5 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOPhLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOPhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 7) + (-(1:ℝ)) := by
      funext y; simp [faceOPhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)), if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)), if_neg (hne 7 6 (by decide)), if_neg (hne 7 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOPhHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceOPhHi ω)
        = fun y => (1 : ℝ) * y (Rv 7) + (-((11:ℝ)/10)) := by
      funext y; simp [faceOPhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)), if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)), if_neg (hne 7 6 (by decide)), if_neg (hne 7 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceVzLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceVzLo ω)
        = fun y => (-1 : ℝ) * y (Rv 9) + (-(1:ℝ)) := by
      funext y; simp [faceVzLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 9) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 9 0 (by decide)), if_neg (hne 9 1 (by decide)), if_neg (hne 9 2 (by decide)), if_neg (hne 9 4 (by decide)), if_neg (hne 9 6 (by decide)), if_neg (hne 9 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceVzHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceVzHi ω)
        = fun y => (1 : ℝ) * y (Rv 9) + (-((11:ℝ)/10)) := by
      funext y; simp [faceVzHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 9) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 9 0 (by decide)), if_neg (hne 9 1 (by decide)), if_neg (hne 9 2 (by decide)), if_neg (hne 9 4 (by decide)), if_neg (hne 9 6 (by decide)), if_neg (hne 9 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceAxLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceAxLo ω)
        = fun y => (-1 : ℝ) * y (Rv 10) + (-(1:ℝ)) := by
      funext y; simp [faceAxLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 10) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 10 0 (by decide)), if_neg (hne 10 1 (by decide)), if_neg (hne 10 2 (by decide)), if_neg (hne 10 4 (by decide)), if_neg (hne 10 6 (by decide)), if_neg (hne 10 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceAxHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceAxHi ω)
        = fun y => (1 : ℝ) * y (Rv 10) + (-((11:ℝ)/10)) := by
      funext y; simp [faceAxHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 10) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 10 0 (by decide)), if_neg (hne 10 1 (by decide)), if_neg (hne 10 2 (by decide)), if_neg (hne 10 4 (by decide)), if_neg (hne 10 6 (by decide)), if_neg (hne 10 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceAyLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceAyLo ω)
        = fun y => (-1 : ℝ) * y (Rv 11) + (-(1:ℝ)) := by
      funext y; simp [faceAyLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 11) (-1) (-(1:ℝ)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 11 0 (by decide)), if_neg (hne 11 1 (by decide)), if_neg (hne 11 2 (by decide)), if_neg (hne 11 4 (by decide)), if_neg (hne 11 6 (by decide)), if_neg (hne 11 8 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceAyHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 12) => Term.eval faceAyHi ω)
        = fun y => (1 : ℝ) * y (Rv 11) + (-((11:ℝ)/10)) := by
      funext y; simp [faceAyHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 11) 1 (-((11:ℝ)/10)) x,
      odeField_RW q hq]
    simp only [if_neg (hne 11 0 (by decide)), if_neg (hne 11 1 (by decide)), if_neg (hne 11 2 (by decide)), if_neg (hne 11 4 (by decide)), if_neg (hne 11 6 (by decide)), if_neg (hne 11 8 (by decide))]
    norm_num

theorem hLip_W (q : ℕ) (hq : q < 3) (ν : State (Var 12)) :
    LipschitzOnWith 3 (odeField (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RW q hq, odeField_RW q hq]
  have hdc : ∀ j : Fin 12, |x (Rv j) - y (Rv j)| ≤ dist x y := by
    intro j
    have h := dist_le_pi_dist x y (Rv j)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  have hcoe : ((3 : NNReal) : ℝ) = 3 := rfl
  have hdecay : ∀ j : Fin 12, |(-1 * x (Rv j)) - (-1 * y (Rv j))| ≤ 3 * dist x y := by
    intro j
    have hdiff : -1 * x (Rv j) - -1 * y (Rv j) = -(x (Rv j) - y (Rv j)) := by ring
    rw [hdiff, abs_neg]
    nlinarith [hdc j]
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : 3 * (cstW q - x (Rv 0)) - 3 * (cstW q - y (Rv 0))
        = -3 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have habs : |(-3 : ℝ)| = 3 := by norm_num
    rw [habs, hcoe]
    nlinarith [hdc 0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    nlinarith [hdc 0, abs_nonneg (x (Rv 0) - y (Rv 0))]
  by_cases hc2 : c = Rv 2
  · subst hc2
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 2
  by_cases hc4 : c = Rv 4
  · subst hc4
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 4
  by_cases hc6 : c = Rv 6
  · subst hc6
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)), if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 6
  by_cases hc8 : c = Rv 8
  · subst hc8
    simp only [if_neg (hne 8 0 (by decide)), if_neg (hne 8 1 (by decide)), if_neg (hne 8 2 (by decide)), if_neg (hne 8 4 (by decide)), if_neg (hne 8 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 8
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc4, if_neg hc6, if_neg hc8]
    rw [hcoe]
    simp [dist_nonneg]

theorem hfbnd_W (q : ℕ) (hq : q < 3) (ν : State (Var 12))
    (hν : ∀ gT' ∈ gsSW, Term.eval gT' ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRW q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro x hx
  rw [Metric.mem_closedBall] at hx
  have hcb : ∀ j : Fin 12, |x (Rv j) - ν (Rv j)| ≤ 1 := by
    intro j
    have h := dist_le_pi_dist x ν (Rv j)
    rw [Real.dist_eq] at h
    linarith
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsSW])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν8 : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsSW])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hx0 : |x (Rv 0)| ≤ 9/5 := by
    have h := hcb 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν8⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hx2 : |x (Rv 2)| ≤ 2 := by
    have h := hcb 2
    have hl : -(1:ℝ)/2 ≤ ν (Rv 2) := by
      have := hν facePsiLo (by simp [gsSW])
      simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
    have hh : ν (Rv 2) ≤ (3:ℝ)/20 := by
      have := hν facePsiHi (by simp [gsSW])
      simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
    have hνb : |ν (Rv 2)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 2)) (ν (Rv 2))
    linarith [abs_le.mp hνb]
  have hx4 : |x (Rv 4)| ≤ 2 := by
    have h := hcb 4
    have hl : -(1:ℝ)/2 ≤ ν (Rv 4) := by
      have := hν faceThLo (by simp [gsSW])
      simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
    have hh : ν (Rv 4) ≤ (3:ℝ)/20 := by
      have := hν faceThHi (by simp [gsSW])
      simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
    have hνb : |ν (Rv 4)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 4)) (ν (Rv 4))
    linarith [abs_le.mp hνb]
  have hx6 : |x (Rv 6)| ≤ 2 := by
    have h := hcb 6
    have hl : -(1:ℝ)/2 ≤ ν (Rv 6) := by
      have := hν facePhLo (by simp [gsSW])
      simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
    have hh : ν (Rv 6) ≤ (3:ℝ)/20 := by
      have := hν facePhHi (by simp [gsSW])
      simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
    have hνb : |ν (Rv 6)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 6)) (ν (Rv 6))
    linarith [abs_le.mp hνb]
  have hx8 : |x (Rv 8)| ≤ 2 := by
    have h := hcb 8
    have hl : -(1:ℝ) ≤ ν (Rv 8) := by
      have := hν faceZLo (by simp [gsSW])
      simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
    have hh : ν (Rv 8) ≤ (3:ℝ)/20 := by
      have := hν faceZHi (by simp [gsSW])
      simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
    have hνb : |ν (Rv 8)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 8)) (ν (Rv 8))
    linarith [abs_le.mp hνb]
  rw [odeField_RW q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  have hdecayb : ∀ j : Fin 12, |x (Rv j)| ≤ 2 → ‖(-1 : ℝ) * x (Rv j)‖ ≤ ((8:NNReal) : ℝ) := by
    intro j hj
    rw [Real.norm_eq_abs, abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hj, abs_nonneg (x (Rv j))]
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cstW q ∧ cstW q ≤ 13/20 := by
      interval_cases q <;> norm_num [cstW]
    rw [abs_le]
    push_cast
    obtain ⟨hcl, hch⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hx0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    push_cast
    linarith [abs_le.mp hx0]
  by_cases hc2 : c = Rv 2
  · subst hc2
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 2 (hx2)
  by_cases hc4 : c = Rv 4
  · subst hc4
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)), if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 4 (hx4)
  by_cases hc6 : c = Rv 6
  · subst hc6
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)), if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 6 (hx6)
  by_cases hc8 : c = Rv 8
  · subst hc8
    simp only [if_neg (hne 8 0 (by decide)), if_neg (hne 8 1 (by decide)), if_neg (hne 8 2 (by decide)), if_neg (hne 8 4 (by decide)), if_neg (hne 8 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 8 (hx8)
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc4, if_neg hc6, if_neg hc8]
    norm_num

theorem esW (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM gW gsW) envW) σ →
      HExistSegB (fLW l) (fRW m) (Term.const 1) domLW domRW dt
        (Function.update σ tgW 0) := by
  intro σ hσ
  have hR : Formula.sat domRW σ := hσ.2.2
  rw [sat_domRW] at hR
  obtain ⟨hd10l, hd10h, hd11l, hd11h, hd7l, hd7h, hd3l, hd3h, hd5l, hd5h, hd6l, hd6h, hd2l, hd2h, hd1l, hd4l, hd4h, hd0l, hd0h, hd9l, hd9h, hd8l, hd8h⟩ := hR
  have hupd : ∀ j : Fin 12, σ (Side.R, j) = Function.update σ tgW 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgW, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsSW, Term.eval gT' (Function.update σ tgW 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsSW, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNW, Term.eval gT' (Function.update σ tgW 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNW, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVzLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVzHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceAxLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceAxHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceAyLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceAyHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratified (fLW l) (fRW m) (Term.const 1)
    domLW domRW gsSW [] gsNW 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLW l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RW gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLW l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RW gT' (List.mem_append_right _ hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x _ hface
      exact hbndS_W m hm gT' hgT x hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      exact hbndN_W m hm i hi x hx)
    (by
      intro x hS hN
      have hS' : ∀ gT' ∈ gsSW, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hb0l : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsSW])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hb0h : x (Rv 0) ≤ (4:ℝ)/5 := by
        have := hS' faceVHi (by simp [gsSW])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hb2l : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsSW])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hb2h : x (Rv 2) ≤ (3:ℝ)/20 := by
        have := hS' facePsiHi (by simp [gsSW])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have hb4l : -(1:ℝ)/2 ≤ x (Rv 4) := by
        have := hS' faceThLo (by simp [gsSW])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have hb4h : x (Rv 4) ≤ (3:ℝ)/20 := by
        have := hS' faceThHi (by simp [gsSW])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hb6l : -(1:ℝ)/2 ≤ x (Rv 6) := by
        have := hS' facePhLo (by simp [gsSW])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hb6h : x (Rv 6) ≤ (3:ℝ)/20 := by
        have := hS' facePhHi (by simp [gsSW])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      have hb8l : -(1:ℝ) ≤ x (Rv 8) := by
        have := hS' faceZLo (by simp [gsSW])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hb8h : x (Rv 8) ≤ (3:ℝ)/20 := by
        have := hS' faceZHi (by simp [gsSW])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hb1l : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNW])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hb3l : -(1:ℝ) ≤ x (Rv 3) := by
        have := hN faceOPsLo (by simp [gsNW])
        simp only [faceOPsLo, Term.eval, AOp.interp] at this; linarith
      have hb3h : x (Rv 3) ≤ (11:ℝ)/10 := by
        have := hN faceOPsHi (by simp [gsNW])
        simp only [faceOPsHi, Term.eval, AOp.interp] at this; linarith
      have hb5l : -(1:ℝ) ≤ x (Rv 5) := by
        have := hN faceOThLo (by simp [gsNW])
        simp only [faceOThLo, Term.eval, AOp.interp] at this; linarith
      have hb5h : x (Rv 5) ≤ (11:ℝ)/10 := by
        have := hN faceOThHi (by simp [gsNW])
        simp only [faceOThHi, Term.eval, AOp.interp] at this; linarith
      have hb7l : -(1:ℝ) ≤ x (Rv 7) := by
        have := hN faceOPhLo (by simp [gsNW])
        simp only [faceOPhLo, Term.eval, AOp.interp] at this; linarith
      have hb7h : x (Rv 7) ≤ (11:ℝ)/10 := by
        have := hN faceOPhHi (by simp [gsNW])
        simp only [faceOPhHi, Term.eval, AOp.interp] at this; linarith
      have hb9l : -(1:ℝ) ≤ x (Rv 9) := by
        have := hN faceVzLo (by simp [gsNW])
        simp only [faceVzLo, Term.eval, AOp.interp] at this; linarith
      have hb9h : x (Rv 9) ≤ (11:ℝ)/10 := by
        have := hN faceVzHi (by simp [gsNW])
        simp only [faceVzHi, Term.eval, AOp.interp] at this; linarith
      have hb10l : -(1:ℝ) ≤ x (Rv 10) := by
        have := hN faceAxLo (by simp [gsNW])
        simp only [faceAxLo, Term.eval, AOp.interp] at this; linarith
      have hb10h : x (Rv 10) ≤ (11:ℝ)/10 := by
        have := hN faceAxHi (by simp [gsNW])
        simp only [faceAxHi, Term.eval, AOp.interp] at this; linarith
      have hb11l : -(1:ℝ) ≤ x (Rv 11) := by
        have := hN faceAyLo (by simp [gsNW])
        simp only [faceAyLo, Term.eval, AOp.interp] at this; linarith
      have hb11h : x (Rv 11) ≤ (11:ℝ)/10 := by
        have := hN faceAyHi (by simp [gsNW])
        simp only [faceAyHi, Term.eval, AOp.interp] at this; linarith
      exact (sat_domRW x).mpr ⟨hb10l, hb10h, hb11l, hb11h, hb7l, hb7h, hb3l, hb3h, hb5l, hb5h, hb6l, hb6h, hb2l, hb2h, hb1l, hb4l, hb4h, hb0l, hb0h, hb9l, hb9h, hb8l, hb8h⟩)
    3 8 1 one_pos
    (fun ν0 _ => hLip_W m hm ν0)
    (fun ν0 h0 => hfbnd_W m hm ν0 (fun gT' hgT => h0 gT' (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgW 0)
    hfS
    hfN
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The route verdicts (stratified-DC over the two components) -/

def VerdW (l m : ℕ) : Prop :=
  ∀ i (hi : i < (gW :: gsW).length),
    z3solve (flowQuery ⟨(gW :: gsW)[i], fLW l, fRW m, Term.const 1,
      strataDomHost (Formula.and domLW domRW) ((gW :: gsW).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gW :: gsW)[i], fLW l, fRW m, Term.const 1,
      strataDomHost (Formula.and domLW domRW) ((gW :: gsW).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gW :: gsW)[i], fLW l, fRW m, Term.const 1,
      strataDomHost (Formula.and domLW domRW) ((gW :: gsW).take i)⟩) = Verdict.unsat

/-! ## The certified couplings -/

theorem coupleW (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdW l m) :
    ∀ σ', Formula.sat (Formula.and (FM gW gsW) envW) σ' → σ' tgW = 0 →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tgW (leftBlock (fLW l))) domLW)
        (Program.ode (rightBlock (fRW m) (Term.const 1)) domRW)
        (Formula.and (FM gW gsW) envW) tgW dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgW (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgW
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLW l) (fRW m) (Term.const 1)
    (Formula.and domLW domRW) (gW :: gsW) hv
  have hboxes : ∀ g' ∈ gW :: gsW, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLW l) ++ rightBlock (fRW m) (Term.const 1))
      (Formula.and domLW domRW)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gW gsW σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gW gsW (fLW l) (fRW m)
    (Term.const 1) domLW domRW tgW dt
    (LR_blocks_disjoint _ _ _ (hfLW l hl) (hfRW m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLW hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRW hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLW l) _ h
      exact aux_ne_Lv aW i hi)
    (fun h => aux_notin_range_Lv aW (leftBlock_readVars_sub (fLW l) (hfLW l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRW m) (Term.const 1) _ h
      exact aux_ne_Rv aW i hi)
    (fun h => aux_notin_range_Rv aW (rightBlock_readVars_sub (fRW m) (Term.const 1)
      (hfRW m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aW (rightBlock_boundSet_sub (fRW m) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aW (hdomLW h))
    (fun h => aux_notin_range_Rv aW (hdomRW h))
    htgg hboxes
    (esW l m hl hm dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLW ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRW μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLW μ := by
    rwa [(Formula.coincidence domLW (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLW hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRW m) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLW μ ↔ Formula.sat domLW ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Static hops and the window response -/

theorem static_hopW (fR : Fin 12 → Term (Var 12)) (lam : Term (Var 12))
    (φ : Formula (Var 12)) (σ : State (Var 12)) (hσφ : Formula.sat φ σ)
    (hdom : Formula.sat (Formula.and domLW domRW) σ) :
    ∃ ρ, Program.sem ((⟨fR, lam, domRW⟩ : RepoHop 12).prog domLW) σ ρ
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

theorem hops_convW : ∀ (ps : List ℕ), (∀ p ∈ ps, p < 3) →
    List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ → Program.sem q ν μ)
      (ps.map (fun p => (⟨fRW p, Term.const 1, domRW⟩ : RepoHop 12).prog domLW))
      (ps.map (fun p => Program.ode (rightBlock (fRW p) (Term.const 1)) domRW)) := by
  intro ps
  induction ps with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hps
      refine List.Forall₂.cons ?_ (ih (fun p hp => hps p (List.mem_cons_of_mem a hp)))
      intro ν μ hrun
      exact joint_run_toR (hfRW a (hps a List.mem_cons_self)) (by simp [Term.fv]) hrun

/-- The window response: static hops up the chain, the certified coupling at the
reached mode. -/
theorem respondW (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdW l m) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 12)} (hσ : Formula.sat (Formula.and (FM gW gsW) envW) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12))
      (windowSeg (leftBlock (fLW l)) domLW tgW dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRW p) (Term.const 1))
          domRW))
        ++ [Program.ode (rightBlock (fRW m) (Term.const 1)) domRW]))
      (Formula.and (FM gW gsW) envW)) σ := by
  have hfa := Hmulti_window1_prefixedF (fLW l) domLW (FM gW gsW) envW aW dt
    htgFW htgenvW
    (path.map (fun p => (⟨fRW p, Term.const 1, domRW⟩ : RepoHop 12)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRW p (hpath p hp), by simp [Term.fv], hdomRW⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact static_hopW (fRW p) (Term.const 1) _ σ' hσ' hσ'.2)
    (hfLW l hl) hdomLW
    (Program.ode (rightBlock (fRW m) (Term.const 1)) domRW)
    (coupleW l m hl hm dt hdt hv)
    hσ
  rw [show (path.map (fun p => (⟨fRW p, Term.const 1, domRW⟩ : RepoHop 12))).map
      (fun h => h.prog domLW)
      = path.map (fun p => (⟨fRW p, Term.const 1, domRW⟩ : RepoHop 12).prog domLW)
    from by rw [List.map_map]; rfl] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono
    (List.rel_append (hops_convW path hpath)
      (List.Forall₂.cons (fun _ _ h => h) List.Forall₂.nil)) ν μ hrun) hfa

/-! ## The step provider (in-place at or ahead, climb from behind) -/

theorem HmultiW (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdW 0 0) (hv01 : VerdW 0 1) (hv02 : VerdW 0 2)
    (hv11 : VerdW 1 1) (hv12 : VerdW 1 2) (hv22 : VerdW 2 2) :
    ∀ P ∈ leftProgsW dt, ∀ (q : ℕ), q < GrW.modes.length → ∀ σ, σ mvW = (q : ℝ) →
      Formula.sat (Formula.and (FM gW gsW) envW) σ →
      ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
        (∀ s ∈ segs, GrW.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrW.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 12)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gW gsW) envW)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrW] using hq
  have hsingle : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12))
      (b : ℕ × RMode (Var 12) × REdge (Var 12)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  simp only [leftProgsW, leftDataW, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  all_goals interval_cases q
  -- window STEEP: every start couples in place
  · exact ⟨[(0, modeW 0, edgeW 0 0)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 0 (by norm_num), edgeW_mem 0 0 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 0 0 (by norm_num) (by norm_num) dt hdt hv00 [] (by simp) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(1, modeW 1, edgeW 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 1 (by norm_num), edgeW_mem 1 1 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 0 1 (by norm_num) (by norm_num) dt hdt hv01 [] (by simp) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(2, modeW 2, edgeW 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 2 (by norm_num), edgeW_mem 2 2 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 0 2 (by norm_num) (by norm_num) dt hdt hv02 [] (by simp) hσ
        simpa [modeW] using this)⟩
  -- window MODER: start STEEP climbs, the rest in place
  · exact ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 1)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrW_modeAt 0 (by norm_num), edgeW_mem 0 1 (by simp [GrW])⟩
        · exact ⟨GrW_modeAt 1 (by norm_num), edgeW_mem 1 1 (by simp [GrW])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 1 1 (by norm_num) (by norm_num) dt hdt hv11 [0]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(1, modeW 1, edgeW 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 1 (by norm_num), edgeW_mem 1 1 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 1 1 (by norm_num) (by norm_num) dt hdt hv11 [] (by simp) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(2, modeW 2, edgeW 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 2 (by norm_num), edgeW_mem 2 2 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 1 2 (by norm_num) (by norm_num) dt hdt hv12 [] (by simp) hσ
        simpa [modeW] using this)⟩
  -- window FLAT: climb to FLAT from behind, in place at FLAT
  · exact ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 2), (2, modeW 2, edgeW 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrW_modeAt 0 (by norm_num), edgeW_mem 0 1 (by simp [GrW])⟩
        · exact ⟨GrW_modeAt 1 (by norm_num), edgeW_mem 1 2 (by simp [GrW])⟩
        · exact ⟨GrW_modeAt 2 (by norm_num), edgeW_mem 2 2 (by simp [GrW])⟩),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 2 2 (by norm_num) (by norm_num) dt hdt hv22 [0, 1]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(1, modeW 1, edgeW 1 2), (2, modeW 2, edgeW 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrW_modeAt 1 (by norm_num), edgeW_mem 1 2 (by simp [GrW])⟩
        · exact ⟨GrW_modeAt 2 (by norm_num), edgeW_mem 2 2 (by simp [GrW])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 2 2 (by norm_num) (by norm_num) dt hdt hv22 [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeW] using this)⟩
  · exact ⟨[(2, modeW 2, edgeW 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrW_modeAt 2 (by norm_num), edgeW_mem 2 2 (by simp [GrW])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondW 2 2 (by norm_num) (by norm_num) dt hdt hv22 [] (by simp) hσ
        simpa [modeW] using this)⟩

/-- **`refinement_ladder_rover_rung1_2to3`, modal Theorem 3** — the first plain
list-invariant instance (multiF chain, climb dispatch, no vacuity). -/
theorem rover_dof_terrain_rung3_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdW 0 0) (hv01 : VerdW 0 1) (hv02 : VerdW 0 2)
    (hv11 : VerdW 1 1) (hv12 : VerdW 1 2) (hv22 : VerdW 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvW)
      (RFormula.and (RFormula.and (canonInvM gW gsW) (envLR domLW domRW))
        (mvValidR mvW GrW.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrW mvW (FM gW gsW) domLW domRW (leftProgsW dt)
    (canonInvM gW gsW) (encode_canonInvM gW gsW) ?_ ?_ ?_
  · exact hdis_multi GrW 0 1 dt leftDataW (by decide) httW hRvW hLW
  · exact hstep_assembled_multiF GrW mvW (FM gW gsW) envW (leftProgsW dt)
      hmvFW hmvenvW hfreshW httW hltW (hframesW dt)
      (HmultiW dt hdt hv00 hv01 hv02 hv11 hv12 hv22)
  · exact hddF_multiE GrW 0 1 dt leftDataW (canonInvM gW gsW) domLW domRW (by decide)
      httW hRvW hLW
      (canonInvM_varsL gW gsW (by
        intro g' hg'
        simp only [gW, gsW, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gW gsW) hdomLW hdomRW


end RoverDofTerrainRung3Modal
end RelCertifier
