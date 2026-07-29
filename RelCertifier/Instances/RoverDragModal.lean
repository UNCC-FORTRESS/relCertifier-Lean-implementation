/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `rover_drag`, modal Theorem 3 with a NONZERO-field existence discharge

The second unconditional instance, and the template-completer: `arm_chain_rung3`'s
landing mode had the zero field (Lie, Lipschitz, and the field bound all trivial);
`rover_drag`'s single mode carries the quadratic drag `vx' = 0.05 − 0.3·vx²`, so this
instance exercises the FULL L1 route on a real field:

* both evolve faces are STRICT (the emitted `--emit-viability3` tags) and discharge
  IN-KERNEL via `lie_affine_coord` + the field value at the pinned face — no Z3;
* the Lipschitz constant (`K = 2` on unit balls around face-region anchors) and the
  field bound (`L = 2`) are hand-proved for the concrete field;
* `HExistSegB_of_viability_stratified` with `gsS = [faceLo, faceHi]`, `gsN = gsG = []`.

One left window (`Cruise`), one right mode (`Track`, identical dynamics), the
self-edge response. `n = 2` pad (the clock and the mode variable need distinct Aux
coordinates); the pad coordinate is inert. Residual: ONE route verdict (`VerdRD`).
Axioms: the standard three + `z3_unsat_sound` at that leaf.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.rover_drag

namespace RelCertifier
namespace RoverDragModal

open DL DLCalTiming DLRel Parse Set

def vsD : List String := ["vx"]
def dummyD : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLD : Parse.PMode := rover_drag_IR.L.modes.getD 0 dummyD
def mRD : Parse.PMode := rover_drag_IR.R.modes.getD 0 dummyD

abbrev mvD : Var 2 := (Side.Aux, 0)
abbrev aD : Fin 2 := (1 : Fin 2)
abbrev tgD : Var 2 := (Side.Aux, aD)

noncomputable def fLD : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.L mLD
noncomputable def fRD : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.R mRD
noncomputable def domLD : Formula (Var 2) := hostEvolve vsD 2 Side.L mLD
noncomputable def domRD : Formula (Var 2) := hostEvolve vsD 2 Side.R mRD
noncomputable def envD : Formula (Var 2) := Formula.and domLD domRD

noncomputable def gD : Term (Var 2) :=
  ((Run.invToG vsD 2 ((rover_drag_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

noncomputable def modeD : RMode (Var 2) :=
  { sys := rightBlock fRD (Term.const 1), dom := domRD, weight := 1 }

def edgeD : REdge (Var 2) :=
  { src := 0, tgt := 0, guard := Formula.tt, pruned := false }

noncomputable def GrD : SearchGraph (Var 2) :=
  { modes := [modeD], edges := [edgeD] }

/-! ## Side-splits -/

theorem fLD_pipe (i : Fin 2) : fLD i =
    (((some mLD).bind (Run.dynOf vsD 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRD_pipe (i : Fin 2) : fRD i =
    (((some mRD).bind (Run.dynOf vsD 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLD_pipe : domLD =
    (((some mLD).bind (fun m => Run.lowerF vsD 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRD_pipe : domRD =
    (((some mRD).bind (fun m => Run.lowerF vsD 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLD : ∀ i, (fLD i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsD) (some mLD)
    (by simp [mLD, rover_drag_IR, Parse.PExpr.namesFree]) i x (fLD_pipe i ▸ hx))

theorem hfRD : ∀ i, (fRD i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsD) (some mRD)
    (by simp [mRD, rover_drag_IR, Parse.PExpr.namesFree]) i x (fRD_pipe i ▸ hx))

theorem hdomLD : domLD.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsD) (some mLD)
    (by simp [mLD, rover_drag_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domLD_pipe ▸ hx))

theorem hdomRD : domRD.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsD) (some mRD)
    (by simp [mRD, rover_drag_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domRD_pipe ▸ hx))

theorem hgD : gD.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgD : mvD ∉ gD.fv := fun h => by
  rcases hgD h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggD : tgD ∉ gD.fv := fun h => by
  rcases hgD h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvD : mvD ∉ envD.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvD : tgD ∉ envD.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## Graph shape facts -/

theorem GrD_modeAt {q : ℕ} {m : RMode (Var 2)} (hm : GrD.modeAt q = some m) :
    q = 0 ∧ m = modeD := by
  match q with
  | 0 => exact ⟨rfl, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, GrD])

theorem httD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_singleton] at hmem
  subst hmem; rfl

theorem hltD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.tgt < GrD.modes.length := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_singleton] at hmem
  subst hmem; norm_num [GrD, edgeD]

theorem hRvD : ∀ q m, GrD.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨-, rfl⟩ := GrD_modeAt hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub fRD (Term.const 1) hy
  · exact rightBlock_readVars_sub fRD (Term.const 1) hfRD (by simp [Term.fv]) hy
  · exact hdomRD hy

theorem edgeD_from : edgeD ∈ GrD.edgesFrom 0 :=
  List.mem_filter.mpr ⟨by simp [GrD], by simp [edgeD]⟩

/-! ## The left window family -/

noncomputable def leftDataD : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLD, domLD, 1)]

noncomputable def leftProgsD (dt : ℝ) : List (Program (Var 2)) :=
  leftDataD.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgD dt d.2.2)

theorem hLD : ∀ d ∈ leftDataD, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataD, List.mem_singleton] at hd
  subst hd
  exact ⟨hfLD, hdomLD⟩

theorem hframesD (dt : ℝ) : ∀ P ∈ leftProgsD dt, FramesMv P mvD := by
  intro P hP
  simp only [leftProgsD, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgD dt d.2.2 mvD (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

theorem hfreshD : ∀ q m, GrD.modeAt q = some m →
    mvD ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvD q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The route-verdict residual -/

def VerdRD : Prop :=
  z3solve (flowQuery ⟨gD, fLD, fRD, Term.const 1,
    Formula.and domLD domRD⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gD, fLD, fRD, Term.const 1,
    Formula.and domLD domRD⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gD, fLD, fRD, Term.const 1,
    Formula.and domLD domRD⟩) = Verdict.unsat

/-! ## The existence discharge — strict faces, nonzero field, Z3-free -/

theorem hpr005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

theorem hpr03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

/-- The lowered right field, coordinate 0: `1/20 − 3/10·vx²` (kernel pin). -/
theorem fRD0_eval (x : State (Var 2)) :
    Term.eval (fRD 0) x = 1/20 - 3/10 * (x (Rv 0) * x (Rv 0)) := by
  simp [fRD, hostDyn, mRD, rover_drag_IR, vsD, Run.dynOf, Run.lowerE, hpr005, hpr03,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The pad coordinate's field is zero. -/
theorem fRD1_eval (x : State (Var 2)) : Term.eval (fRD 1) x = 0 := by
  simp [fRD, hostDyn, mRD, rover_drag_IR, vsD, Run.dynOf, Run.lowerE, hpr005, hpr03,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

/-- The faces (`vx_R ∈ [0, 7/5]`): `−vx_R` and `vx_R − 7/5`. -/
noncomputable def faceLoD : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceHiD : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((7:ℝ)/5))

theorem faces_fv_RD : ∀ gT ∈ [faceLoD, faceHiD], ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  rcases List.mem_cons.mp hgT with rfl | hgT
  · simp only [faceLoD, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩
  · rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceHiD, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

/-- The frozen-left joint system at `Track` — the `vx_R` row is the drag field, all
other rows are zero. -/
theorem odeField_RD (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) fRD (Term.const 1)) x
      = fun c => if c = Rv 0 then 1/20 - 3/10 * (x (Rv 0) * x (Rv 0)) else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) fRD (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) fRD (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) fRD (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) fRD (Term.const 1),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have : (Lv j : Var 2) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, this]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRD0_eval]
      · have : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRD1_eval, this]
  · have hcR : c ≠ Rv 0 := by
      intro hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp only [odeField, if_neg hc, if_neg hcR]

/-- Strict inflow on the lower face (`vx_R = 0` ⟹ `Lie = −1/20 < 0`). -/
theorem hbndS_lo (x : State (Var 2))
    (hface : Term.eval faceLoD x = 0) :
    Lie (jointSys (fun _ => Term.const 0) fRD (Term.const 1))
      (fun ω => Term.eval faceLoD ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceLoD, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceLoD ω)
      = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
    funext y
    simp [faceLoD, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
    odeField_RD]
  simp only [if_pos rfl, hx0]
  norm_num

/-- Strict inflow on the upper face (`vx_R = 7/5` ⟹ `Lie = 1/20 − 3/10·49/25 < 0`). -/
theorem hbndS_hi (x : State (Var 2))
    (hface : Term.eval faceHiD x = 0) :
    Lie (jointSys (fun _ => Term.const 0) fRD (Term.const 1))
      (fun ω => Term.eval faceHiD ω) x < 0 := by
  have hx0 : x (Rv 0) = 7/5 := by
    simp only [faceHiD, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceHiD ω)
      = fun y => (1 : ℝ) * y (Rv 0) + (-(7/5)) := by
    funext y
    simp [faceHiD, Term.eval, AOp.interp]
    ring
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(7/5)) x,
    odeField_RD]
  simp only [if_pos rfl, hx0]
  norm_num

/-- Hand Lipschitz bound: on unit balls around face-region anchors, the field is
`2`-Lipschitz (the only nonzero row is `1/20 − 3/10·v²` with `|v| ≤ 12/5`). -/
theorem hLip_RD (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLoD, faceHiD], Term.eval gT ν ≤ 0) :
    LipschitzOnWith 2 (odeField (jointSys (fun _ => Term.const 0) fRD (Term.const 1)))
      (Metric.closedBall ν 1) := by
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceLoD List.mem_cons_self
    simp only [faceLoD, Term.eval, AOp.interp] at this
    linarith
  have hν14 : ν (Rv 0) ≤ 7/5 := by
    have := hν faceHiD (by simp)
    simp only [faceHiD, Term.eval, AOp.interp] at this
    linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_RD, odeField_RD]
  rw [Metric.mem_closedBall] at hx hy
  have hνb : |ν (Rv 0)| ≤ 7/5 := abs_le.mpr ⟨by linarith, hν14⟩
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have hyc : |y (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist y ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hy
  have hxb : |x (Rv 0)| ≤ 12/5 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith
  have hyb : |y (Rv 0)| ≤ 12/5 := by
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 0)) (ν (Rv 0))
    linarith
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_true]
    rw [Real.dist_eq]
    have hdiff : (1/20 - 3/10 * (x (Rv 0) * x (Rv 0)))
        - (1/20 - 3/10 * (y (Rv 0) * y (Rv 0)))
        = -(3/10) * (x (Rv 0) + y (Rv 0)) * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul, abs_mul]
    have h2 : |x (Rv 0) + y (Rv 0)| ≤ 24/5 := by
      calc |x (Rv 0) + y (Rv 0)| ≤ |x (Rv 0)| + |y (Rv 0)| := abs_add_le _ _
        _ ≤ 24/5 := by linarith
    have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
      have h := dist_le_pi_dist x y (Rv 0)
      rwa [Real.dist_eq] at h
    have hd : (0:ℝ) ≤ dist x y := dist_nonneg
    have habs : |(-(3/10) : ℝ)| = 3/10 := by norm_num
    have hstep : |(-(3/10) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (3/10) * (24/5) * dist x y := by
      rw [habs]
      have hnn : (0:ℝ) ≤ |x (Rv 0) - y (Rv 0)| := abs_nonneg _
      nlinarith [abs_nonneg (x (Rv 0) + y (Rv 0))]
    have hcoe : ((2 : NNReal) : ℝ) = 2 := rfl
    calc |(-(3/10) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (3/10) * (24/5) * dist x y := hstep
      _ ≤ ((2 : NNReal) : ℝ) * dist x y := by rw [hcoe]; nlinarith
  · simp only [if_neg hc]
    simp [dist_nonneg]

/-- Hand field bound: `‖field‖ ≤ 2` on the same balls. -/
theorem hfbnd_RD (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLoD, faceHiD], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) fRD (Term.const 1)) x‖ ≤ (2:NNReal) := by
  intro x hx
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceLoD List.mem_cons_self
    simp only [faceLoD, Term.eval, AOp.interp] at this
    linarith
  have hν14 : ν (Rv 0) ≤ 7/5 := by
    have := hν faceHiD (by simp)
    simp only [faceHiD, Term.eval, AOp.interp] at this
    linarith
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at this
    linarith
  have hxb : |x (Rv 0)| ≤ 12/5 := by
    have := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    have hνb : |ν (Rv 0)| ≤ 7/5 := abs_le.mpr ⟨by linarith, hν14⟩
    linarith [abs_le.mp hνb]
  rw [odeField_RD]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_pos rfl, Real.norm_eq_abs]
    have hsq : x (Rv 0) * x (Rv 0) ≤ (12/5) * (12/5) := by
      have := abs_le.mp hxb
      nlinarith
    have hsq0 : 0 ≤ x (Rv 0) * x (Rv 0) := mul_self_nonneg _
    rw [abs_le]
    push_cast
    refine ⟨by nlinarith [hsq, hsq0], by nlinarith [hsq, hsq0]⟩
  · simp only [if_neg hc]
    norm_num

/-- **The existence residual, discharged Z3-free**: both faces strict, quadratic
field, hand analytic data. -/
theorem esRD (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (invLe gD) envD) σ →
      HExistSegB fLD fRD (Term.const 1) domLD domRD dt
        (Function.update σ tgD 0) := by
  intro σ hσ
  have hfaces : ∀ gT ∈ [faceLoD, faceHiD],
      Term.eval gT (Function.update σ tgD 0) ≤ 0 := by
    have hR : Formula.sat domRD σ := hσ.2.2
    have hlow : Run.lowerF vsD 2 Side.R mRD.evolve =
        some (IForm.and
          (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0))
          (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat ((7:ℚ)/5)))) := by
      simp [Run.lowerF, mRD, rover_drag_IR, vsD, Run.lowerE, Run.resolveVar,
        hpr00, hpr14, List.findIdx?_cons]
    have hshape : domRD = Formula.and
        (Formula.cmp .ge (Term.var (Side.R, 0)) (Term.const ((0:ℚ):ℝ)))
        (Formula.cmp .le (Term.var (Side.R, 0)) (Term.const (((7:ℚ)/5):ℝ))) := by
      rw [domRD_pipe]
      simp [hlow, IForm.toHost, ITerm.toHost]
    rw [hshape] at hR
    obtain ⟨h1, h2⟩ := hR
    simp only [Formula.sat, CompOp.interp, Term.eval] at h1 h2
    push_cast at h1 h2
    intro gT hgT
    have hupd : σ (Side.R, (0 : Fin 2)) = Function.update σ tgD 0 (Side.R, 0) := by
      rw [Function.update_of_ne (by simp [tgD, Prod.ext_iff])]
    rcases List.mem_cons.mp hgT with rfl | hgT
    · simp only [faceLoD, Term.eval, AOp.interp, Rv]
      rw [← hupd]
      linarith
    · rw [List.mem_singleton] at hgT
      subst hgT
      simp only [faceHiD, Term.eval, AOp.interp, Rv]
      rw [← hupd]
      linarith
  refine HExistSegB_of_viability_stratified fLD fRD (Term.const 1)
    domLD domRD [faceLoD, faceHiD] [] [] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fLD _ hb
      obtain ⟨j, hj⟩ := faces_fv_RD gT hgT x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro gT hgT x _ hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_lo x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      have h0 : 0 ≤ x (Rv 0) := by
        have := hS faceLoD (by simp [List.mem_append])
        simp only [faceLoD, Term.eval, AOp.interp] at this
        linarith
      have h14 : x (Rv 0) ≤ 7/5 := by
        have := hS faceHiD (by simp [List.mem_append])
        simp only [faceHiD, Term.eval, AOp.interp] at this
        linarith
      have hlow : Run.lowerF vsD 2 Side.R mRD.evolve =
          some (IForm.and
            (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0))
            (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat ((7:ℚ)/5)))) := by
        simp [Run.lowerF, mRD, rover_drag_IR, vsD, Run.lowerE, Run.resolveVar,
          hpr00, hpr14, List.findIdx?_cons]
      have hshape : domRD = Formula.and
          (Formula.cmp .ge (Term.var (Side.R, 0)) (Term.const ((0:ℚ):ℝ)))
          (Formula.cmp .le (Term.var (Side.R, 0)) (Term.const (((7:ℚ)/5):ℝ))) := by
        rw [domRD_pipe]
        simp [hlow, IForm.toHost, ITerm.toHost]
      rw [hshape]
      refine ⟨?_, ?_⟩ <;>
        · show CompOp.interp _ _ _
          push_cast [CompOp.interp, Term.eval]
          first
            | simpa [Rv] using h0
            | simpa [Rv] using h14)
    2 2 1 one_pos
    (fun ν0 h0 => hLip_RD ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    (fun ν0 h0 => hfbnd_RD ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgD 0)
    hfaces
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The coupling, the provider, and the gate -/

theorem coupleRD (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdRD) :
    ∀ σ', Formula.sat (Formula.and (invLe gD) envD) σ' → σ' tgD = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgD (leftBlock fLD)) domLD)
        (Program.ode (rightBlock fRD (Term.const 1)) domRD)
        (Formula.and (invLe gD) envD) tgD dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgD (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgD
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' fLD fRD (Term.const 1)
    (Formula.and domLD domRD) [gD]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdRD] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock fLD ++ rightBlock fRD (Term.const 1))
      (Formula.and domLD domRD)) (invLe gD)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gD
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gD σ').mp hσ'.1
  have hbase := segment_faModalB_from_certB gD fLD fRD (Term.const 1)
    domLD domRD tgD dt
    (LR_blocks_disjoint _ _ _ hfLD hfRD (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRD hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fLD _ h
      exact aux_ne_Lv aD i hi)
    (fun h => aux_notin_range_Lv aD (leftBlock_readVars_sub fLD hfLD h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub fRD (Term.const 1) _ h
      exact aux_ne_Rv aD i hi)
    (fun h => aux_notin_range_Rv aD (rightBlock_readVars_sub fRD (Term.const 1)
      hfRD (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aD (rightBlock_boundSet_sub fRD (Term.const 1) h))
    (fun h => aux_notin_range_Lv aD (hdomLD h))
    (fun h => aux_notin_range_Rv aD (hdomRD h))
    htggD hbox (esRD dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLD ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRD μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLD μ := by
    rwa [(Formula.coincidence domLD (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub fRD (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLD μ ↔ Formula.sat domLD ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem seg_selfRD (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdRD)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gD) envD) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock fLD) domLD tgD dt 1)
      (bigSeq ([((0 : ℕ), modeD, edgeD)].map
        (fun s => Program.ode s.2.1.sys s.2.1.dom)))
      (Formula.and (invLe gD) envD)) σ := by
  have hfa := Hmulti_window1_prefixed fLD domLD gD envD aD dt htggD htgenvD []
    (by simp) (by simp) hfLD hdomLD
    (Program.ode (rightBlock fRD (Term.const 1)) domRD)
    (coupleRD dt hdt hv) hσ
  simpa [modeD] using hfa

theorem HmultiRD (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdRD) :
    ∀ P ∈ leftProgsD dt, ∀ (q : ℕ), q < GrD.modes.length → ∀ σ, σ mvD = (q : ℝ) →
      Formula.sat (Formula.and (invLe gD) envD) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gD) envD)) σ := by
  intro P hP q hq σ hmv hσ
  have hq0 : q = 0 := by simpa [GrD] using hq
  subst hq0
  simp only [leftProgsD, leftDataD, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl
  exact ⟨[(0, modeD, edgeD)],
    (by
      intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      exact ⟨rfl, edgeD_from⟩),
    (by simp),
    (fun s hs => by
      have : s = (0, modeD, edgeD) := by simpa [List.head?_cons] using hs.symm
      rw [this]),
    seg_selfRD dt hdt hv hσ⟩

/-- **`rover_drag`, modal Theorem 3, existence DISCHARGED on a nonzero field.**
Residual: one route verdict. -/
theorem rover_drag_modal (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdRD) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsD dt))
      (rightAutomatonBody GrD mvD)
      (RFormula.and (RFormula.and (canonInv gD) (envLR domLD domRD))
        (mvValidR mvD GrD.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrD mvD gD domLD domRD (leftProgsD dt)
    (canonInv gD) (encode_canonInv gD) ?_ ?_ ?_
  · exact hdis_multi GrD 0 1 dt leftDataD (by decide) httD hRvD hLD
  · exact hstep_assembled_multiE GrD mvD gD envD (leftProgsD dt) hmvgD hmvenvD
      hfreshD httD hltD (hframesD dt)
      (HmultiRD dt hdt hv)
  · exact hddF_multiE GrD 0 1 dt leftDataD (canonInv gD) domLD domRD (by decide)
      httD hRvD hLD (canonInv_varsL gD hgD) (canonInv_varsR gD) hdomLD hdomRD

end RoverDragModal
end RelCertifier
