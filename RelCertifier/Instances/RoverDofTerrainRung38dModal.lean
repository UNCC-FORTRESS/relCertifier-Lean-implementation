/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3+ — `rover_dof_terrain_rung3_8d`, modal Theorem 3 (multiF at n = 8)

The terrain multiF pattern at eight coordinates: the right carries four decaying
rows (`ψ, θ, z, φ` — eight strict faces beyond the velocity pair) and two
zero-field rate rows (`ω_ψ, ω_θ` — four zero-Lie non-strict faces), same one-way
chain, same two-component tolerance, same climb dispatch. Existence Z3-free
(`K = 3`, `L = 8`). Residuals: six stratified-DC packs (`VerdT8 l m`).
Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3_8d

namespace RelCertifier
namespace RoverDofTerrainRung38dModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsU : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
def dummyU : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLU (l : ℕ) : Parse.PMode := rover_dof_terrain_rung3_8d_IR.L.modes.getD l dummyU
def mRU (q : ℕ) : Parse.PMode := rover_dof_terrain_rung3_8d_IR.R.modes.getD q dummyU

abbrev mvU : Var 8 := (Side.Aux, 0)
abbrev aU : Fin 8 := (1 : Fin 8)
abbrev tgU : Var 8 := (Side.Aux, aU)

noncomputable def fLU (l : ℕ) : Fin 8 → Term (Var 8) := hostDyn vsU 8 Side.L (mLU l)
noncomputable def fRU (q : ℕ) : Fin 8 → Term (Var 8) := hostDyn vsU 8 Side.R (mRU q)
noncomputable def domLU : Formula (Var 8) := hostEvolve vsU 8 Side.L (mLU 0)
noncomputable def domRU : Formula (Var 8) := hostEvolve vsU 8 Side.R (mRU 0)
noncomputable def envU : Formula (Var 8) := Formula.and domLU domRU

def atomsOf : Parse.PForm → List Parse.PForm
  | .and x y => atomsOf x ++ atomsOf y
  | f => [f]

def invUPF : Parse.PForm :=
  (rover_dof_terrain_rung3_8d_IR.invariants.getD 0 ("", Parse.PForm.tt)).2

noncomputable def gAt (i : ℕ) : Term (Var 8) :=
  ((Run.invToG vsU 8 ((atomsOf invUPF).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def gU : Term (Var 8) := gAt 0
noncomputable def gsU : List (Term (Var 8)) := [gAt 1]

/-! ## Side-splits -/

theorem fLU_pipe (l : ℕ) (i : Fin 8) : fLU l i =
    (((some (mLU l)).bind (Run.dynOf vsU 8 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRU_pipe (q : ℕ) (i : Fin 8) : fRU q i =
    (((some (mRU q)).bind (Run.dynOf vsU 8 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLU_pipe : domLU =
    (((some (mLU 0)).bind (fun m => Run.lowerF vsU 8 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRU_pipe : domRU =
    (((some (mRU 0)).bind (fun m => Run.lowerF vsU 8 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLU (l : ℕ) (hl : l < 3) : ∀ i, (fLU l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsU) (some (mLU l))
    (by interval_cases l <;>
      simp [mLU, rover_dof_terrain_rung3_8d_IR, Parse.PExpr.namesFree]) i x
    (fLU_pipe l i ▸ hx))

theorem hfRU (q : ℕ) (hq : q < 3) : ∀ i, (fRU q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsU) (some (mRU q))
    (by interval_cases q <;>
      simp [mRU, rover_dof_terrain_rung3_8d_IR, Parse.PExpr.namesFree]) i x
    (fRU_pipe q i ▸ hx))

theorem hdomLU : domLU.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsU) (some (mLU 0))
    (by simp [mLU, rover_dof_terrain_rung3_8d_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLU_pipe ▸ hx))

theorem hdomRU : domRU.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsU) (some (mRU 0))
    (by simp [mRU, rover_dof_terrain_rung3_8d_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRU_pipe ▸ hx))

theorem hgAt (i : ℕ) : (gAt i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvg : ∀ g' ∈ gU :: gsU, mvU ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem htgg : ∀ g' ∈ gU :: gsU, tgU ∉ g'.fv := by
  intro g' hg' h
  have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
    simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl <;> exact hgAt _
  rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem hmvFU : mvU ∉ (FM gU gsU).fv := notMem_FM_fv hmvg
theorem htgFU : tgU ∉ (FM gU gsU).fv := notMem_FM_fv htgg

theorem hmvenvU : mvU ∉ envU.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLU h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRU h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvU : tgU ∉ envU.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLU h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRU h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph -/

noncomputable def modeU (q : ℕ) : RMode (Var 8) :=
  { sys := rightBlock (fRU q) (Term.const 1), dom := domRU, weight := 1 }

def edgeU (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrU : SearchGraph (Var 8) :=
  { modes := [modeU 0, modeU 1, modeU 2],
    edges := [edgeU 0 1, edgeU 0 0, edgeU 1 2, edgeU 1 1, edgeU 2 2] }

theorem GrU_modeAt (q : ℕ) (hq : q < 3) : GrU.modeAt q = some (modeU q) := by
  interval_cases q <;> rfl

theorem httU : ∀ q, ∀ e ∈ GrU.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrU.edges := List.mem_of_mem_filter he
  simp only [GrU, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltU : ∀ q, ∀ e ∈ GrU.edgesFrom q, e.tgt < GrU.modes.length := by
  intro q e he
  have hmem : e ∈ GrU.edges := List.mem_of_mem_filter he
  simp only [GrU, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrU, edgeU]

theorem hRvU : ∀ q m, GrU.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeU q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrU] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrU] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrU] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrU])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRU q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRU q) (Term.const 1) (hfRU q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRU hy

theorem edgeU_mem : ∀ st tgt, edgeU st tgt ∈ GrU.edges →
    edgeU st tgt ∈ GrU.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeU]⟩

theorem hfreshU : ∀ q m, GrU.modeAt q = some m →
    mvU ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvU q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataU : List ((Fin 8 → Term (Var 8)) × Formula (Var 8) × ℕ) :=
  [(fLU 0, domLU, 1), (fLU 1, domLU, 1), (fLU 2, domLU, 1)]

noncomputable def leftProgsU (dt : ℝ) : List (Program (Var 8)) :=
  leftDataU.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgU dt d.2.2)

theorem hLU : ∀ d ∈ leftDataU, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataU, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLU 0 (by norm_num), hdomLU⟩
  · exact ⟨hfLU 1 (by norm_num), hdomLU⟩
  · exact ⟨hfLU 2 (by norm_num), hdomLU⟩

theorem hframesU (dt : ℝ) : ∀ P ∈ leftProgsU dt, FramesMv P mvU := by
  intro P hP
  simp only [leftProgsU, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgU dt d.2.2 mvU (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hu030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hu050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hu065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hu3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hum1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hu0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hu00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hu08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hu02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hum05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hu015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hum10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hu11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Field and shape pins -/

noncomputable def cstU (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRU0_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 0) x = 3 * (cstU q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cstU]

theorem fRU1_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU2_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU3_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 3) x = 0 := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU4_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU5_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 5) x = 0 := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU6_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU7_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 7) x = -1 * x (Rv 7) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRU (x : State (Var 8)) : Formula.sat domRU x ↔
    (-(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ 11/10 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 11/10 ∧
     -(1:ℝ)/2 ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3/20 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/20) := by
  simp only [domRU, hostEvolve, mRU, rover_dof_terrain_rung3_8d_IR, vsU]
  simp [Run.lowerF, Run.lowerE, hum05, hu015, hu00, hu08, hum10, hu11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

theorem gAt0_eval (x : State (Var 8)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invUPF, rover_dof_terrain_rung3_8d_IR, Run.invToG,
    Run.lowerE, vsU, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 8)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invUPF, rover_dof_terrain_rung3_8d_IR, Run.invToG,
    Run.lowerE, vsU, hu02, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-! ## Existence -/

noncomputable def faceVLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((4:ℝ)/5))
noncomputable def facePsiLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 2))
noncomputable def facePsiHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 2)) (Term.const ((3:ℝ)/20))
noncomputable def faceThLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 4))
noncomputable def faceThHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 4)) (Term.const ((3:ℝ)/20))
noncomputable def faceZLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 6))
noncomputable def faceZHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 6)) (Term.const ((3:ℝ)/20))
noncomputable def facePhLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ)/2)) (Term.var (Rv 7))
noncomputable def facePhHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 7)) (Term.const ((3:ℝ)/20))
noncomputable def faceSLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))
noncomputable def faceOPsLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 3))
noncomputable def faceOPsHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 3)) (Term.const ((11:ℝ)/10))
noncomputable def faceOThLo : Term (Var 8) :=
  Term.binop AOp.sub (Term.const (-(1:ℝ))) (Term.var (Rv 5))
noncomputable def faceOThHi : Term (Var 8) :=
  Term.binop AOp.sub (Term.var (Rv 5)) (Term.const ((11:ℝ)/10))

noncomputable def gsSU : List (Term (Var 8)) :=
  [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi,
   faceZLo, faceZHi, facePhLo, facePhHi]
noncomputable def gsNU : List (Term (Var 8)) :=
  [faceSLo, faceOPsLo, faceOPsHi, faceOThLo, faceOThHi]

theorem faces_fv_RU : ∀ gT' ∈ gsSU ++ gsNU, ∀ x ∈ gT'.fv, x ∈ range Rv := by
  intro gT' hgT x hx
  simp only [gsSU, gsNU, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl <;>
    · simp only [faceVLo, faceVHi, facePsiLo, facePsiHi, faceThLo, faceThHi,
        faceZLo, faceZHi, facePhLo, facePhHi, faceSLo, faceOPsLo, faceOPsHi,
        faceOThLo, faceOThHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false,
        false_or, or_false, Set.mem_singleton_iff] at hx
      exact ⟨_, hx.symm⟩

theorem odeField_RU (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    odeField (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)) x
      = fun c =>
        if c = Rv 0 then 3 * (cstU q - x (Rv 0))
        else if c = Rv 1 then x (Rv 0)
        else if c = Rv 2 then -1 * x (Rv 2)
        else if c = Rv 4 then -1 * x (Rv 4)
        else if c = Rv 6 then -1 * x (Rv 6)
        else if c = Rv 7 then -1 * x (Rv 7)
        else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have h0 : (Lv j : Var 8) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      have h1 : (Lv j : Var 8) ≠ Rv 1 := by simp [Lv, Rv, Prod.ext_iff]
      have h2 : (Lv j : Var 8) ≠ Rv 2 := by simp [Lv, Rv, Prod.ext_iff]
      have h4 : (Lv j : Var 8) ≠ Rv 4 := by simp [Lv, Rv, Prod.ext_iff]
      have h6 : (Lv j : Var 8) ≠ Rv 6 := by simp [Lv, Rv, Prod.ext_iff]
      have h7 : (Lv j : Var 8) ≠ Rv 7 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, h0, h1, h2, h4, h6, h7]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      fin_cases j
      · simp [Term.eval, AOp.interp, fRU0_eval q hq]
      · simp [Term.eval, AOp.interp, fRU1_eval q hq,
          hne 1 0 (by decide)]
      · simp [Term.eval, AOp.interp, fRU2_eval q hq,
          hne 2 0 (by decide), hne 2 1 (by decide)]
      · simp [Term.eval, AOp.interp, fRU3_eval q hq,
          hne 3 0 (by decide), hne 3 1 (by decide), hne 3 2 (by decide),
          hne 3 4 (by decide), hne 3 6 (by decide), hne 3 7 (by decide)]
      · simp [Term.eval, AOp.interp, fRU4_eval q hq,
          hne 4 0 (by decide), hne 4 1 (by decide), hne 4 2 (by decide)]
      · simp [Term.eval, AOp.interp, fRU5_eval q hq,
          hne 5 0 (by decide), hne 5 1 (by decide), hne 5 2 (by decide),
          hne 5 4 (by decide), hne 5 6 (by decide), hne 5 7 (by decide)]
      · simp [Term.eval, AOp.interp, fRU6_eval q hq,
          hne 6 0 (by decide), hne 6 1 (by decide), hne 6 2 (by decide),
          hne 6 4 (by decide)]
      · simp [Term.eval, AOp.interp, fRU7_eval q hq,
          hne 7 0 (by decide), hne 7 1 (by decide), hne 7 2 (by decide),
          hne 7 4 (by decide), hne 7 6 (by decide)]
  · have hnotR : ∀ j : Fin 8, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hnotR 0), if_neg (hnotR 1),
      if_neg (hnotR 2), if_neg (hnotR 4), if_neg (hnotR 6), if_neg (hnotR 7)]

theorem hbndS_U (q : ℕ) (hq : q < 3) : ∀ gT' ∈ gsSU, ∀ x : State (Var 8),
    Term.eval gT' x = 0 →
    Lie (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1))
      (fun ω => Term.eval gT' ω) x < 0 := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro gT' hgT x hface
  simp only [gsSU, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hx0 : x (Rv 0) = 0 := by
      simp only [faceVLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceVLo ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
      funext y; simp [faceVLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
      odeField_RU q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstU]
  · have hx0 : x (Rv 0) = 4/5 := by
      simp only [faceVHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceVHi ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-(4/5)) := by
      funext y; simp [faceVHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(4/5)) x,
      odeField_RU q hq]
    simp only [eq_self_iff_true, if_true, if_pos rfl, hx0]
    interval_cases q <;> norm_num [cstU]
  · have hx : x (Rv 2) = -(1:ℝ)/2 := by
      simp only [facePsiLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePsiLo ω)
        = fun y => (-1 : ℝ) * y (Rv 2) + (-(1/2)) := by
      funext y; simp [facePsiLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) (-1) (-(1/2)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 2) = (3:ℝ)/20 := by
      simp only [facePsiHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePsiHi ω)
        = fun y => (1 : ℝ) * y (Rv 2) + (-(3/20)) := by
      funext y; simp [facePsiHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 2) 1 (-(3/20)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = -(1:ℝ)/2 := by
      simp only [faceThLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 4) + (-(1/2)) := by
      funext y; simp [faceThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) (-1) (-(1/2)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
      if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 4) = (3:ℝ)/20 := by
      simp only [faceThHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceThHi ω)
        = fun y => (1 : ℝ) * y (Rv 4) + (-(3/20)) := by
      funext y; simp [faceThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 4) 1 (-(3/20)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
      if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 6) = -(1:ℝ) := by
      simp only [faceZLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceZLo ω)
        = fun y => (-1 : ℝ) * y (Rv 6) + (-1) := by
      funext y; simp [faceZLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) (-1) (-1) x,
      odeField_RU q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 6) = (3:ℝ)/20 := by
      simp only [faceZHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval faceZHi ω)
        = fun y => (1 : ℝ) * y (Rv 6) + (-(3/20)) := by
      funext y; simp [faceZHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 6) 1 (-(3/20)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 7) = -(1:ℝ)/2 := by
      simp only [facePhLo, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePhLo ω)
        = fun y => (-1 : ℝ) * y (Rv 7) + (-(1/2)) := by
      funext y; simp [facePhLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) (-1) (-(1/2)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)),
      if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)),
      if_neg (hne 7 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num
  · have hx : x (Rv 7) = (3:ℝ)/20 := by
      simp only [facePhHi, Term.eval, AOp.interp] at hface; linarith
    have hfun : (fun ω : State (Var 8) => Term.eval facePhHi ω)
        = fun y => (1 : ℝ) * y (Rv 7) + (-(3/20)) := by
      funext y; simp [facePhHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 7) 1 (-(3/20)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)),
      if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)),
      if_neg (hne 7 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl, hx]
    norm_num

theorem hbndN_U (q : ℕ) (hq : q < 3) : ∀ i (hi : i < gsNU.length), ∀ x : State (Var 8),
    (∀ gT' ∈ gsSU ++ ([] : List (Term (Var 8))), Term.eval gT' x ≤ 0) →
    Lie (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1))
      (fun ω => Term.eval gsNU[i] ω) x ≤ 0 := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro i hi x hx
  have hi5 : i < 5 := by simpa [gsNU] using hi
  have hv0 : 0 ≤ x (Rv 0) := by
    have := hx faceVLo (List.mem_append_left _ (by simp [gsSU]))
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  interval_cases i
  · show Lie _ (fun ω => Term.eval faceSLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval faceSLo ω)
        = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [faceSLo, Term.eval, AOp.interp]
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
      odeField_RU q hq]
    simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    linarith
  · show Lie _ (fun ω => Term.eval faceOPsLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval faceOPsLo ω)
        = fun y => (-1 : ℝ) * y (Rv 3) + (-1) := by
      funext y; simp [faceOPsLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) (-1) (-1) x,
      odeField_RU q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)),
      if_neg (hne 3 2 (by decide)), if_neg (hne 3 4 (by decide)),
      if_neg (hne 3 6 (by decide)), if_neg (hne 3 7 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOPsHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval faceOPsHi ω)
        = fun y => (1 : ℝ) * y (Rv 3) + (-(11/10)) := by
      funext y; simp [faceOPsHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 3) 1 (-(11/10)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 3 0 (by decide)), if_neg (hne 3 1 (by decide)),
      if_neg (hne 3 2 (by decide)), if_neg (hne 3 4 (by decide)),
      if_neg (hne 3 6 (by decide)), if_neg (hne 3 7 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOThLo ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval faceOThLo ω)
        = fun y => (-1 : ℝ) * y (Rv 5) + (-1) := by
      funext y; simp [faceOThLo, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) (-1) (-1) x,
      odeField_RU q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)),
      if_neg (hne 5 2 (by decide)), if_neg (hne 5 4 (by decide)),
      if_neg (hne 5 6 (by decide)), if_neg (hne 5 7 (by decide))]
    norm_num
  · show Lie _ (fun ω => Term.eval faceOThHi ω) x ≤ 0
    have hfun : (fun ω : State (Var 8) => Term.eval faceOThHi ω)
        = fun y => (1 : ℝ) * y (Rv 5) + (-(11/10)) := by
      funext y; simp [faceOThHi, Term.eval, AOp.interp]; ring
    rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 5) 1 (-(11/10)) x,
      odeField_RU q hq]
    simp only [if_neg (hne 5 0 (by decide)), if_neg (hne 5 1 (by decide)),
      if_neg (hne 5 2 (by decide)), if_neg (hne 5 4 (by decide)),
      if_neg (hne 5 6 (by decide)), if_neg (hne 5 7 (by decide))]
    norm_num

theorem hLip_U (q : ℕ) (hq : q < 3) (ν : State (Var 8)) :
    LipschitzOnWith 3 (odeField (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)))
      (Metric.closedBall ν 1) := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RU q hq, odeField_RU q hq]
  have hdc : ∀ j : Fin 8, |x (Rv j) - y (Rv j)| ≤ dist x y := by
    intro j
    have h := dist_le_pi_dist x y (Rv j)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  have hcoe : ((3 : NNReal) : ℝ) = 3 := rfl
  have hdecay : ∀ j : Fin 8, |(-1 * x (Rv j)) - (-1 * y (Rv j))| ≤ 3 * dist x y := by
    intro j
    have hdiff : -1 * x (Rv j) - -1 * y (Rv j) = -(x (Rv j) - y (Rv j)) := by ring
    rw [hdiff, abs_neg]
    nlinarith [hdc j]
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq]
    have hdiff : 3 * (cstU q - x (Rv 0)) - 3 * (cstU q - y (Rv 0))
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
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 2
  by_cases hc4 : c = Rv 4
  · subst hc4
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
      if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 4
  by_cases hc6 : c = Rv 6
  · subst hc6
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 6
  by_cases hc7 : c = Rv 7
  · subst hc7
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)),
      if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)),
      if_neg (hne 7 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    rw [Real.dist_eq, hcoe]
    exact hdecay 7
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc4, if_neg hc6,
      if_neg hc7]
    rw [hcoe]
    simp [dist_nonneg]

theorem hfbnd_U (q : ℕ) (hq : q < 3) (ν : State (Var 8))
    (hν : ∀ gT' ∈ gsSU, Term.eval gT' ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1)) x‖
        ≤ ((8:NNReal) : ℝ) := by
  have hne : ∀ (a b : Fin 8), a ≠ b → (Rv a : Var 8) ≠ Rv b := by
    intro a b hab
    simp [Rv, Prod.ext_iff]
    exact fun h => hab (by exact_mod_cast h)
  intro x hx
  rw [Metric.mem_closedBall] at hx
  have hcb : ∀ j : Fin 8, |x (Rv j) - ν (Rv j)| ≤ 1 := by
    intro j
    have h := dist_le_pi_dist x ν (Rv j)
    rw [Real.dist_eq] at h
    linarith
  have hband : ∀ (j : Fin 8) (lo hi : ℝ), lo ≤ ν (Rv j) → ν (Rv j) ≤ hi →
      -1 ≤ lo → hi ≤ 3/20 → |x (Rv j)| ≤ 2 := by
    intro j lo hi hl hh hlo1 hhi1
    have h := hcb j
    have hνb : |ν (Rv j)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv j)) (ν (Rv j))
    linarith [abs_le.mp hνb]
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo (by simp [gsSU])
    simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
  have hν8 : ν (Rv 0) ≤ 4/5 := by
    have := hν faceVHi (by simp [gsSU])
    simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
  have hx0 : |x (Rv 0)| ≤ 9/5 := by
    have h := hcb 0
    have hνb : |ν (Rv 0)| ≤ 4/5 := abs_le.mpr ⟨by linarith, hν8⟩
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith [abs_le.mp hνb]
  have hx2 : |x (Rv 2)| ≤ 2 := by
    refine hband 2 (-(1:ℝ)/2) (3/20) ?_ ?_ (by norm_num) (by norm_num)
    · have := hν facePsiLo (by simp [gsSU])
      simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
    · have := hν facePsiHi (by simp [gsSU])
      simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
  have hx4 : |x (Rv 4)| ≤ 2 := by
    refine hband 4 (-(1:ℝ)/2) (3/20) ?_ ?_ (by norm_num) (by norm_num)
    · have := hν faceThLo (by simp [gsSU])
      simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
    · have := hν faceThHi (by simp [gsSU])
      simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
  have hx6 : |x (Rv 6)| ≤ 2 := by
    refine hband 6 (-(1:ℝ)) (3/20) ?_ ?_ (by norm_num) (by norm_num)
    · have := hν faceZLo (by simp [gsSU])
      simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
    · have := hν faceZHi (by simp [gsSU])
      simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
  have hx7 : |x (Rv 7)| ≤ 2 := by
    refine hband 7 (-(1:ℝ)/2) (3/20) ?_ ?_ (by norm_num) (by norm_num)
    · have := hν facePhLo (by simp [gsSU])
      simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
    · have := hν facePhHi (by simp [gsSU])
      simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
  rw [odeField_RU q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  have hdecayb : ∀ j : Fin 8, |x (Rv j)| ≤ 2 → ‖(-1 : ℝ) * x (Rv j)‖ ≤ ((8:NNReal) : ℝ) := by
    intro j hj
    rw [Real.norm_eq_abs, abs_mul]
    push_cast
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs]
    linarith [abs_le.mp hj, abs_nonneg (x (Rv j))]
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [eq_self_iff_true, if_true, if_pos rfl, Real.norm_eq_abs]
    have hcst : 0 ≤ cstU q ∧ cstU q ≤ 13/20 := by
      interval_cases q <;> norm_num [cstU]
    rw [abs_le]
    push_cast
    obtain ⟨hc1, hc2⟩ := hcst
    constructor <;> nlinarith [abs_le.mp hx0]
  by_cases hc1 : c = Rv 1
  · subst hc1
    simp only [if_neg (hne 1 0 (by decide)), eq_self_iff_true, if_true, if_pos rfl,
      Real.norm_eq_abs]
    push_cast
    linarith [abs_le.mp hx0]
  by_cases hc2 : c = Rv 2
  · subst hc2
    simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 2 hx2
  by_cases hc4 : c = Rv 4
  · subst hc4
    simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
      if_neg (hne 4 2 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 4 hx4
  by_cases hc6 : c = Rv 6
  · subst hc6
    simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
      if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
      eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 6 hx6
  by_cases hc7 : c = Rv 7
  · subst hc7
    simp only [if_neg (hne 7 0 (by decide)), if_neg (hne 7 1 (by decide)),
      if_neg (hne 7 2 (by decide)), if_neg (hne 7 4 (by decide)),
      if_neg (hne 7 6 (by decide)), eq_self_iff_true, if_true, if_pos rfl]
    exact hdecayb 7 hx7
  · simp only [if_neg hc0, if_neg hc1, if_neg hc2, if_neg hc4, if_neg hc6,
      if_neg hc7]
    norm_num

theorem esU (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (FM gU gsU) envU) σ →
      HExistSegB (fLU l) (fRU m) (Term.const 1) domLU domRU dt
        (Function.update σ tgU 0) := by
  intro σ hσ
  have hR : Formula.sat domRU σ := hσ.2.2
  rw [sat_domRU] at hR
  obtain ⟨h3l, h3h, h5l, h5h, h7l, h7h, h2l, h2h, h1l, h4l, h4h, h0l, h0h, h6l, h6h⟩ := hR
  have hupd : ∀ j : Fin 8, σ (Side.R, j) = Function.update σ tgU 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgU, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsSU, Term.eval gT' (Function.update σ tgU 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsSU, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNU, Term.eval gT' (Function.update σ tgU 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNU, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratified (fLU l) (fRU m) (Term.const 1)
    domLU domRU gsSU [] gsNU 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLU l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RU gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLU l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RU gT' (List.mem_append_right _ hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x _ hface
      exact hbndS_U m hm gT' hgT x hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      exact hbndN_U m hm i hi x hx)
    (by
      intro x hS hN
      have hS' : ∀ gT' ∈ gsSU, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hv0 : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsSU])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hv8 : x (Rv 0) ≤ 4/5 := by
        have := hS' faceVHi (by simp [gsSU])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hp1 : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsSU])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hp2 : x (Rv 2) ≤ 3/20 := by
        have := hS' facePsiHi (by simp [gsSU])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have hth1 : -(1:ℝ)/2 ≤ x (Rv 4) := by
        have := hS' faceThLo (by simp [gsSU])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have hth2 : x (Rv 4) ≤ 3/20 := by
        have := hS' faceThHi (by simp [gsSU])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hz1 : -(1:ℝ) ≤ x (Rv 6) := by
        have := hS' faceZLo (by simp [gsSU])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hz2 : x (Rv 6) ≤ 3/20 := by
        have := hS' faceZHi (by simp [gsSU])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hph1 : -(1:ℝ)/2 ≤ x (Rv 7) := by
        have := hS' facePhLo (by simp [gsSU])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hph2 : x (Rv 7) ≤ 3/20 := by
        have := hS' facePhHi (by simp [gsSU])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      have hs0 : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNU])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hop1 : -(1:ℝ) ≤ x (Rv 3) := by
        have := hN faceOPsLo (by simp [gsNU])
        simp only [faceOPsLo, Term.eval, AOp.interp] at this; linarith
      have hop2 : x (Rv 3) ≤ 11/10 := by
        have := hN faceOPsHi (by simp [gsNU])
        simp only [faceOPsHi, Term.eval, AOp.interp] at this; linarith
      have hot1 : -(1:ℝ) ≤ x (Rv 5) := by
        have := hN faceOThLo (by simp [gsNU])
        simp only [faceOThLo, Term.eval, AOp.interp] at this; linarith
      have hot2 : x (Rv 5) ≤ 11/10 := by
        have := hN faceOThHi (by simp [gsNU])
        simp only [faceOThHi, Term.eval, AOp.interp] at this; linarith
      exact (sat_domRU x).mpr ⟨hop1, hop2, hot1, hot2, hph1, hph2, hp1, hp2,
        hs0, hth1, hth2, hv0, hv8, hz1, hz2⟩)
    3 8 1 one_pos
    (fun ν0 _ => hLip_U m hm ν0)
    (fun ν0 h0 => hfbnd_U m hm ν0 (fun gT' hgT => h0 gT' (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgU 0)
    hfS
    hfN
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The route verdicts (stratified-DC over the two components) -/

def VerdU (l m : ℕ) : Prop :=
  ∀ i (hi : i < (gU :: gsU).length),
    z3solve (flowQuery ⟨(gU :: gsU)[i], fLU l, fRU m, Term.const 1,
      strataDomHost (Formula.and domLU domRU) ((gU :: gsU).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gU :: gsU)[i], fLU l, fRU m, Term.const 1,
      strataDomHost (Formula.and domLU domRU) ((gU :: gsU).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gU :: gsU)[i], fLU l, fRU m, Term.const 1,
      strataDomHost (Formula.and domLU domRU) ((gU :: gsU).take i)⟩) = Verdict.unsat

/-! ## The certified couplings -/

theorem coupleU (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdU l m) :
    ∀ σ', Formula.sat (Formula.and (FM gU gsU) envU) σ' → σ' tgU = 0 →
      faModalB (Equiv.refl (Var 8))
        (Program.ode (DLCalTiming.clk tgU (leftBlock (fLU l))) domLU)
        (Program.ode (rightBlock (fRU m) (Term.const 1)) domRU)
        (Formula.and (FM gU gsU) envU) tgU dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgU (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgU
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLU l) (fRU m) (Term.const 1)
    (Formula.and domLU domRU) (gU :: gsU) hv
  have hboxes : ∀ g' ∈ gU :: gsU, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLU l) ++ rightBlock (fRU m) (Term.const 1))
      (Formula.and domLU domRU)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gU gsU σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gU gsU (fLU l) (fRU m)
    (Term.const 1) domLU domRU tgU dt
    (LR_blocks_disjoint _ _ _ (hfLU l hl) (hfRU m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLU hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRU hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLU l) _ h
      exact aux_ne_Lv aU i hi)
    (fun h => aux_notin_range_Lv aU (leftBlock_readVars_sub (fLU l) (hfLU l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRU m) (Term.const 1) _ h
      exact aux_ne_Rv aU i hi)
    (fun h => aux_notin_range_Rv aU (rightBlock_readVars_sub (fRU m) (Term.const 1)
      (hfRU m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aU (rightBlock_boundSet_sub (fRU m) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aU (hdomLU h))
    (fun h => aux_notin_range_Rv aU (hdomRU h))
    htgg hboxes
    (esU l m hl hm dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLU ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRU μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLU μ := by
    rwa [(Formula.coincidence domLU (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLU hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRU m) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLU μ ↔ Formula.sat domLU ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Static hops and the window response -/

theorem static_hopU (fR : Fin 8 → Term (Var 8)) (lam : Term (Var 8))
    (φ : Formula (Var 8)) (σ : State (Var 8)) (hσφ : Formula.sat φ σ)
    (hdom : Formula.sat (Formula.and domLU domRU) σ) :
    ∃ ρ, Program.sem ((⟨fR, lam, domRU⟩ : RepoHop 8).prog domLU) σ ρ
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

theorem hops_convU : ∀ (ps : List ℕ), (∀ p ∈ ps, p < 3) →
    List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ → Program.sem q ν μ)
      (ps.map (fun p => (⟨fRU p, Term.const 1, domRU⟩ : RepoHop 8).prog domLU))
      (ps.map (fun p => Program.ode (rightBlock (fRU p) (Term.const 1)) domRU)) := by
  intro ps
  induction ps with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hps
      refine List.Forall₂.cons ?_ (ih (fun p hp => hps p (List.mem_cons_of_mem a hp)))
      intro ν μ hrun
      exact joint_run_toR (hfRU a (hps a List.mem_cons_self)) (by simp [Term.fv]) hrun

/-- The window response: static hops up the chain, the certified coupling at the
reached mode. -/
theorem respondU (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdU l m) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 8)} (hσ : Formula.sat (Formula.and (FM gU gsU) envU) σ) :
    Formula.sat (faModal (Equiv.refl (Var 8))
      (windowSeg (leftBlock (fLU l)) domLU tgU dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRU p) (Term.const 1))
          domRU))
        ++ [Program.ode (rightBlock (fRU m) (Term.const 1)) domRU]))
      (Formula.and (FM gU gsU) envU)) σ := by
  have hfa := Hmulti_window1_prefixedF (fLU l) domLU (FM gU gsU) envU aU dt
    htgFU htgenvU
    (path.map (fun p => (⟨fRU p, Term.const 1, domRU⟩ : RepoHop 8)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRU p (hpath p hp), by simp [Term.fv], hdomRU⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact static_hopU (fRU p) (Term.const 1) _ σ' hσ' hσ'.2)
    (hfLU l hl) hdomLU
    (Program.ode (rightBlock (fRU m) (Term.const 1)) domRU)
    (coupleU l m hl hm dt hdt hv)
    hσ
  rw [show (path.map (fun p => (⟨fRU p, Term.const 1, domRU⟩ : RepoHop 8))).map
      (fun h => h.prog domLU)
      = path.map (fun p => (⟨fRU p, Term.const 1, domRU⟩ : RepoHop 8).prog domLU)
    from by rw [List.map_map]; rfl] at hfa
  exact sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono
    (List.rel_append (hops_convU path hpath)
      (List.Forall₂.cons (fun _ _ h => h) List.Forall₂.nil)) ν μ hrun) hfa

/-! ## The step provider (in-place at or ahead, climb from behind) -/

theorem HmultiU (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdU 0 0) (hv01 : VerdU 0 1) (hv02 : VerdU 0 2)
    (hv11 : VerdU 1 1) (hv12 : VerdU 1 2) (hv22 : VerdU 2 2) :
    ∀ P ∈ leftProgsU dt, ∀ (q : ℕ), q < GrU.modes.length → ∀ σ, σ mvU = (q : ℝ) →
      Formula.sat (Formula.and (FM gU gsU) envU) σ →
      ∃ segs : List (ℕ × RMode (Var 8) × REdge (Var 8)),
        (∀ s ∈ segs, GrU.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrU.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 8)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gU gsU) envU)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrU] using hq
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
  simp only [leftProgsU, leftDataU, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  all_goals interval_cases q
  -- window STEEP: every start couples in place
  · exact ⟨[(0, modeU 0, edgeU 0 0)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 0 (by norm_num), edgeU_mem 0 0 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 0 0 (by norm_num) (by norm_num) dt hdt hv00 [] (by simp) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(1, modeU 1, edgeU 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 1 (by norm_num), edgeU_mem 1 1 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 0 1 (by norm_num) (by norm_num) dt hdt hv01 [] (by simp) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(2, modeU 2, edgeU 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 2 (by norm_num), edgeU_mem 2 2 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 0 2 (by norm_num) (by norm_num) dt hdt hv02 [] (by simp) hσ
        simpa [modeU] using this)⟩
  -- window MODER: start STEEP climbs, the rest in place
  · exact ⟨[(0, modeU 0, edgeU 0 1), (1, modeU 1, edgeU 1 1)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrU_modeAt 0 (by norm_num), edgeU_mem 0 1 (by simp [GrU])⟩
        · exact ⟨GrU_modeAt 1 (by norm_num), edgeU_mem 1 1 (by simp [GrU])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 1 1 (by norm_num) (by norm_num) dt hdt hv11 [0]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(1, modeU 1, edgeU 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 1 (by norm_num), edgeU_mem 1 1 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 1 1 (by norm_num) (by norm_num) dt hdt hv11 [] (by simp) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(2, modeU 2, edgeU 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 2 (by norm_num), edgeU_mem 2 2 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 1 2 (by norm_num) (by norm_num) dt hdt hv12 [] (by simp) hσ
        simpa [modeU] using this)⟩
  -- window FLAT: climb to FLAT from behind, in place at FLAT
  · exact ⟨[(0, modeU 0, edgeU 0 1), (1, modeU 1, edgeU 1 2), (2, modeU 2, edgeU 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact ⟨GrU_modeAt 0 (by norm_num), edgeU_mem 0 1 (by simp [GrU])⟩
        · exact ⟨GrU_modeAt 1 (by norm_num), edgeU_mem 1 2 (by simp [GrU])⟩
        · exact ⟨GrU_modeAt 2 (by norm_num), edgeU_mem 2 2 (by simp [GrU])⟩),
      hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 2 2 (by norm_num) (by norm_num) dt hdt hv22 [0, 1]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> norm_num) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(1, modeU 1, edgeU 1 2), (2, modeU 2, edgeU 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨GrU_modeAt 1 (by norm_num), edgeU_mem 1 2 (by simp [GrU])⟩
        · exact ⟨GrU_modeAt 2 (by norm_num), edgeU_mem 2 2 (by simp [GrU])⟩),
      hstep _ _ _ rfl (hsingle _),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 2 2 (by norm_num) (by norm_num) dt hdt hv22 [1]
          (by intro p hp; rw [List.mem_singleton] at hp; subst hp; norm_num) hσ
        simpa [modeU] using this)⟩
  · exact ⟨[(2, modeU 2, edgeU 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨GrU_modeAt 2 (by norm_num), edgeU_mem 2 2 (by simp [GrU])⟩),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := respondU 2 2 (by norm_num) (by norm_num) dt hdt hv22 [] (by simp) hσ
        simpa [modeU] using this)⟩

/-- **`refinement_ladder_rover_rung1_2to3`, modal Theorem 3** — the first plain
list-invariant instance (multiF chain, climb dispatch, no vacuity). -/
theorem rover_dof_terrain_rung3_8d_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdU 0 0) (hv01 : VerdU 0 1) (hv02 : VerdU 0 2)
    (hv11 : VerdU 1 1) (hv12 : VerdU 1 2) (hv22 : VerdU 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsU dt))
      (rightAutomatonBody GrU mvU)
      (RFormula.and (RFormula.and (canonInvM gU gsU) (envLR domLU domRU))
        (mvValidR mvU GrU.modes.length))) := by
  refine theorem3_faithful_multiF_LR GrU mvU (FM gU gsU) domLU domRU (leftProgsU dt)
    (canonInvM gU gsU) (encode_canonInvM gU gsU) ?_ ?_ ?_
  · exact hdis_multi GrU 0 1 dt leftDataU (by decide) httU hRvU hLU
  · exact hstep_assembled_multiF GrU mvU (FM gU gsU) envU (leftProgsU dt)
      hmvFU hmvenvU hfreshU httU hltU (hframesU dt)
      (HmultiU dt hdt hv00 hv01 hv02 hv11 hv12 hv22)
  · exact hddF_multiE GrU 0 1 dt leftDataU (canonInvM gU gsU) domLU domRU (by decide)
      httU hRvU hLU
      (canonInvM_varsL gU gsU (by
        intro g' hg'
        simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gU gsU) hdomLU hdomRU


end RoverDofTerrainRung38dModal
end RelCertifier