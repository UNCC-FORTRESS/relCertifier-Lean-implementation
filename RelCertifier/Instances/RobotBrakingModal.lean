/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 (GENERATED family: mid — affine Hold landing) — `robot_braking`, the first UNCONDITIONAL modal Theorem 3

`rvalid (theorem3Form …)` with the existence residual DISCHARGED IN-FILE: the only
remaining hypotheses are the two per-window joint route verdicts (`Verd3`) — the
frozen-contract Z3 leaves. No `hES`.

Structure: two left windows (`Accelerate`, `Brake`), the four-mode right automaton
(`ApproachA → ApproachB → ApproachC → Hold` with self-loops). EVERY response lands at
`Hold` (`jointOK` for both windows, per the emitted cover): joint starts answer with
the self-edge piece there; other starts open with STATIC reposition hops along the
declared chain (zero-duration, certificate-free — the envelope is universal).

Existence at `Hold` is where the L1 chain fires: the mode's evolve faces are both
NON-STRICT (`θ' = 0` — the emitted `--emit-viability3` tags are `nonstrict1` with an
EMPTY strict core), so `HExistSegB_of_viability_stratified` applies with `gsS = []`,
`gsG = []`, and the two faces as the single non-strict stratum. The right field is
identically zero, so the Lie bounds, the Lipschitz data, and the field bound are all
discharged in-kernel — the existence residual costs NO Z3 verdicts here.

Residuals: `Verd3 0`, `Verd3 1`. Axioms: the standard three + `z3_unsat_sound` where
the verdicts enter.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.robot_braking

namespace RelCertifier
namespace RobotBrakingModal

open DL DLCalTiming DLRel Parse Set

def vsA : List String := ["v"]
def dummyA : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLA (l : ℕ) : Parse.PMode := robot_braking_IR.L.modes.getD l dummyA
def mRA (q : ℕ) : Parse.PMode := robot_braking_IR.R.modes.getD q dummyA

abbrev mvA : Var 2 := (Side.Aux, 0)
abbrev aA : Fin 2 := (1 : Fin 2)
abbrev tgA : Var 2 := (Side.Aux, aA)

/-- Lowered fields and domains (`n = 2`; the left is genuinely 2-D, the right's `v`
row is inert). -/
noncomputable def fLA (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsA 2 Side.L (mLA l)
noncomputable def fRA (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsA 2 Side.R (mRA q)
noncomputable def domLA : Formula (Var 2) := hostEvolve vsA 2 Side.L (mLA 0)
noncomputable def domRA : Formula (Var 2) := hostEvolve vsA 2 Side.R (mRA 0)

/-- The joint universal envelope — the loop invariant's conditioning conjunct. -/
noncomputable def envA : Formula (Var 2) := Formula.and domLA domRA

/-- The invariant term (`L_theta − (R_theta + 0.15)`). -/
noncomputable def gA : Term (Var 2) :=
  ((Run.invToG vsA 2 ((robot_braking_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-- Universal evolve: all mode evolves lower identically (kernel facts). -/
theorem domLA_univ (l : ℕ) (hl : l < 1) : hostEvolve vsA 2 Side.L (mLA l) = domLA := by
  interval_cases l <;> rfl
theorem domRA_univ (q : ℕ) (hq : q < 3) : hostEvolve vsA 2 Side.R (mRA q) = domRA := by
  interval_cases q <;> rfl

/-- The right automaton graph. -/
noncomputable def modeA (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRA q) (Term.const 1), dom := domRA, weight := 1 }

def edgeA (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

noncomputable def GrA : SearchGraph (Var 2) :=
  { modes := [modeA 0, modeA 1, modeA 2]
    edges := [edgeA 0 1, edgeA 0 0, edgeA 1 2, edgeA 1 1, edgeA 2 2] }

/-! ## Side-splits (kernel facts via the lowering pipelines) -/

theorem fLA_pipe (l : ℕ) (i : Fin 2) : fLA l i =
    (((some (mLA l)).bind (Run.dynOf vsA 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRA_pipe (q : ℕ) (i : Fin 2) : fRA q i =
    (((some (mRA q)).bind (Run.dynOf vsA 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLA_pipe : domLA =
    (((some (mLA 0)).bind (fun m => Run.lowerF vsA 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRA_pipe : domRA =
    (((some (mRA 0)).bind (fun m => Run.lowerF vsA 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLA (l : ℕ) (hl : l < 1) : ∀ i, ((fLA l) i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsA) (some (mLA l))
    (by interval_cases l <;> simp [mLA, robot_braking_IR, Parse.PExpr.namesFree]) i x
    (fLA_pipe l i ▸ hx))

theorem hfRA (q : ℕ) (hq : q < 3) : ∀ i, ((fRA q) i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsA) (some (mRA q))
    (by interval_cases q <;> simp [mRA, robot_braking_IR, Parse.PExpr.namesFree]) i x
    (fRA_pipe q i ▸ hx))

theorem hdomLA : domLA.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsA) (some (mLA 0))
    (by simp [mLA, robot_braking_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domLA_pipe ▸ hx))

theorem hdomRA : domRA.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsA) (some (mRA 0))
    (by simp [mRA, robot_braking_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domRA_pipe ▸ hx))

theorem hgA : gA.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgA : mvA ∉ gA.fv := fun h => by
  rcases hgA h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggA : tgA ∉ gA.fv := fun h => by
  rcases hgA h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvA : mvA ∉ envA.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLA h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRA h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvA : tgA ∉ envA.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLA h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRA h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## Graph shape facts -/

theorem GrA_modeAt {q : ℕ} {m : RMode (Var 2)} (hm : GrA.modeAt q = some m) :
    q < 3 ∧ m = modeA q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrA])

theorem httA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.tgt < GrA.modes.length := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrA, edgeA]

theorem hRvA : ∀ q m, GrA.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := GrA_modeAt hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRA q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRA q) (Term.const 1) (hfRA q hq) (by simp [Term.fv]) hy
  · exact hdomRA hy

theorem edgeA_from {s t : ℕ} (h : edgeA s t ∈ GrA.edges) : edgeA s t ∈ GrA.edgesFrom s :=
  List.mem_filter.mpr ⟨h, by simp [edgeA]⟩

/-! ## The left window family -/

noncomputable def leftDataA : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLA 0, domLA, 1)]

noncomputable def leftProgsA (dt : ℝ) : List (Program (Var 2)) :=
  leftDataA.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgA dt d.2.2)

theorem hLA : ∀ d ∈ leftDataA, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataA, List.mem_singleton] at hd
  subst hd
  exact ⟨hfLA 0 (by norm_num), hdomLA⟩

theorem hframesA (dt : ℝ) : ∀ P ∈ leftProgsA dt, FramesMv P mvA := by
  intro P hP
  simp only [leftProgsA, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgA dt d.2.2 mvA (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

theorem hfreshA : ∀ q m, GrA.modeAt q = some m →
    mvA ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvA q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The route-verdict residual -/

/-- The per-window joint verdict at the landing mode `Hold` (index 3): the tool's
stratified three-route query family at λ = 1 over the joint universal envelope. -/
def Verd3 (l : ℕ) : Prop :=
  z3solve (flowQuery ⟨gA, fLA l, fRA 2, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gA, fLA l, fRA 2, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gA, fLA l, fRA 2, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat

/-! ## The existence discharge — strict faces, affine field, Z3-free -/

theorem hpr00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr365 : Run.parseRat "3.65" = some ((73:ℚ)/20) := by
  have h : parseQ "3.65" = some (⟨365, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

theorem hlowM : Run.lowerF vsA 2 Side.R (mRA 0).evolve =
    some (IForm.and
      (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0))
      (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat ((73:ℚ)/20)))) := by
  simp [Run.lowerF, mRA, robot_braking_IR, vsA, Run.lowerE, Run.resolveVar,
    hpr00, hpr365, List.findIdx?_cons]

theorem domRA_shape : domRA = Formula.and
    (Formula.cmp .ge (Term.var (Side.R, 0)) (Term.const ((0:ℚ):ℝ)))
    (Formula.cmp .le (Term.var (Side.R, 0)) (Term.const (((73:ℚ)/20):ℝ))) := by
  rw [domRA_pipe]
  simp [hlowM, IForm.toHost, ITerm.toHost]

theorem hpr05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

/-- The lowered `Hold` field, coordinate 0: `1/2·(3/5 − θ)` (kernel pin). -/
theorem fRA2_eval (x : State (Var 2)) :
    Term.eval (fRA 2 0) x = 1/2 * (1 - x (Rv 0)) := by
  simp [fRA, hostDyn, mRA, robot_braking_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
    hpr10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]

theorem fRA2_pad_eval (x : State (Var 2)) : Term.eval (fRA 2 1) x = 0 := by
  simp [fRA, hostDyn, mRA, robot_braking_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
    hpr10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

noncomputable def faceLo : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceHi : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((73:ℝ)/20))

theorem faces_fv_R : ∀ gT ∈ [faceLo, faceHi], ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  rcases List.mem_cons.mp hgT with rfl | hgT
  · simp only [faceLo, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩
  · rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

theorem odeField_M (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1)) x
      = fun c => if c = Rv 0 then 1/2 * (1 - x (Rv 0)) else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1)).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1)) x c
        = ((jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1)).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRA 2)
        (Term.const 1), p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have : (Lv j : Var 2) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, this]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fRA2_eval]
      · have : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fRA2_pad_eval, this]
  · have hcR : c ≠ Rv 0 := by
      intro hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp only [odeField, if_neg hc, if_neg hcR]

theorem hbndS_lo (x : State (Var 2))
    (hface : Term.eval faceLo x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1))
      (fun ω => Term.eval faceLo ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceLo, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceLo ω)
      = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
    funext y
    simp [faceLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
    odeField_M]
  norm_num [hx0]

theorem hbndS_hi (x : State (Var 2))
    (hface : Term.eval faceHi x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRA 2) (Term.const 1))
      (fun ω => Term.eval faceHi ω) x < 0 := by
  have hx0 : x (Rv 0) = 73/20 := by
    simp only [faceHi, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceHi ω)
      = fun y => (1 : ℝ) * y (Rv 0) + (-(73/20)) := by
    funext y
    simp [faceHi, Term.eval, AOp.interp]
    ring
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(73/20)) x,
    odeField_M]
  norm_num [hx0]

theorem hLip_M (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    LipschitzOnWith 1 (odeField (jointSys (fun _ => Term.const 0) (fRA 2)
      (Term.const 1))) (Metric.closedBall ν 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_M, odeField_M]
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_true]
    rw [Real.dist_eq]
    have hdiff : 1/2 * (1 - x (Rv 0)) - 1/2 * (1 - y (Rv 0))
        = -(1/2) * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
      have h := dist_le_pi_dist x y (Rv 0)
      rwa [Real.dist_eq] at h
    have hd : (0:ℝ) ≤ dist x y := dist_nonneg
    have habs : |(-(1/2) : ℝ)| = 1/2 := by norm_num
    have hcoe : ((1 : NNReal) : ℝ) = 1 := rfl
    calc |(-(1/2) : ℝ)| * |x (Rv 0) - y (Rv 0)| ≤ (1/2) * dist x y := by
          rw [habs]; nlinarith
      _ ≤ ((1 : NNReal) : ℝ) * dist x y := by rw [hcoe]; linarith
  · simp only [if_neg hc]
    simp [dist_nonneg]

theorem hfbnd_M (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRA 2)
        (Term.const 1)) x‖ ≤ (3:NNReal) := by
  intro x hx
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceLo List.mem_cons_self
    simp only [faceLo, Term.eval, AOp.interp] at this
    linarith
  have hν12 : ν (Rv 0) ≤ 73/20 := by
    have := hν faceHi (by simp)
    simp only [faceHi, Term.eval, AOp.interp] at this
    linarith
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have hνb : |ν (Rv 0)| ≤ 73/20 := abs_le.mpr ⟨by linarith, hν12⟩
  have hxb : |x (Rv 0)| ≤ 93/20 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith
  rw [odeField_M]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_true, Real.norm_eq_abs]
    have := abs_le.mp hxb
    rw [abs_le]
    push_cast
    constructor <;> nlinarith
  · simp only [if_neg hc]
    norm_num

theorem esA (l : ℕ) (hl : l < 1) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (invLe gA) envA) σ →
      HExistSegB (fLA l) (fRA 2) (Term.const 1) domLA domRA dt
        (Function.update σ tgA 0) := by
  intro σ hσ
  have hfaces : ∀ gT ∈ [faceLo, faceHi],
      Term.eval gT (Function.update σ tgA 0) ≤ 0 := by
    have hR : Formula.sat domRA σ := hσ.2.2
    rw [domRA_shape] at hR
    obtain ⟨h1, h2⟩ := hR
    simp only [Formula.sat, CompOp.interp, Term.eval] at h1 h2
    push_cast at h1 h2
    intro gT hgT
    have hupd : σ (Side.R, (0 : Fin 2)) = Function.update σ tgA 0 (Side.R, 0) := by
      rw [Function.update_of_ne (by simp [tgA, Prod.ext_iff])]
    rcases List.mem_cons.mp hgT with rfl | hgT
    · simp only [faceLo, Term.eval, AOp.interp, Rv]
      rw [← hupd]
      linarith
    · rw [List.mem_singleton] at hgT
      subst hgT
      simp only [faceHi, Term.eval, AOp.interp, Rv]
      rw [← hupd]
      linarith
  have build : ∀ fL : Fin 2 → Term (Var 2), (∀ i, (fL i).fv ⊆ range Lv) →
      HExistSegB fL (fRA 2) (Term.const 1) domLA domRA dt
        (Function.update σ tgA 0) := by
    intro fL hfL
    refine HExistSegB_of_viability_stratified fL (fRA 2) (Term.const 1)
      domLA domRA [faceLo, faceHi] [] [] 0 le_rfl
      (jointSys_wellFormed _ _ _)
      (by
        intro gT hgT x hx hb
        obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ hb
        obtain ⟨j, hj⟩ := faces_fv_R gT hgT x hx
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
          have := hS faceLo (by simp [List.mem_append])
          simp only [faceLo, Term.eval, AOp.interp] at this
          linarith
        have h12 : x (Rv 0) ≤ 73/20 := by
          have := hS faceHi (by simp [List.mem_append])
          simp only [faceHi, Term.eval, AOp.interp] at this
          linarith
        rw [domRA_shape]
        refine ⟨?_, ?_⟩ <;>
          · show CompOp.interp _ _ _
            push_cast [CompOp.interp, Term.eval]
            first
              | simpa [Rv] using h0
              | simpa [Rv] using h12)
      1 3 1 one_pos
      (fun ν0 h0 => hLip_M ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
      (fun ν0 h0 => hfbnd_M ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
      dt hdt
      (Function.update σ tgA 0)
      hfaces
      (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
      (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
  exact build (fLA l) (hfLA l hl)

/-! ## The per-pair bounded coupling (cert-sourced, envelope-strengthened) -/

theorem coupleA {l : ℕ} (hl : l < 1) (dt : ℝ) (hdt : 0 ≤ dt) (hv : Verd3 l) :
    ∀ σ', Formula.sat (Formula.and (invLe gA) envA) σ' → σ' tgA = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgA (leftBlock (fLA l))) domLA)
        (Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA)
        (Formula.and (invLe gA) envA) tgA dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgA (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgA
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLA l) (fRA 2) (Term.const 1)
    (Formula.and domLA domRA) [gA]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, Verd3] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLA l) ++ rightBlock (fRA 2) (Term.const 1))
      (Formula.and domLA domRA)) (invLe gA)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gA
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gA σ').mp hσ'.1
  have hbase := segment_faModalB_from_certB gA (fLA l) (fRA 2) (Term.const 1)
    domLA domRA tgA dt
    (LR_blocks_disjoint _ _ _ (hfLA l hl) (hfRA 2 (by norm_num)) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLA hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRA hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ h
      exact aux_ne_Lv aA i hi)
    (fun h => aux_notin_range_Lv aA (leftBlock_readVars_sub (fLA l) (hfLA l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRA 2) (Term.const 1) _ h
      exact aux_ne_Rv aA i hi)
    (fun h => aux_notin_range_Rv aA (rightBlock_readVars_sub (fRA 2) (Term.const 1)
      (hfRA 2 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aA (rightBlock_boundSet_sub (fRA 2) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aA (hdomLA h))
    (fun h => aux_notin_range_Rv aA (hdomRA h))
    htggA hbox (esA l hl dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLA ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRA μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLA μ := by
    rwa [(Formula.coincidence domLA (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLA hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRA 2) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLA μ ↔ Formula.sat domLA ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Per-(window, start) responses — every response lands at `Hold` -/

/-- Start `Hold` (3): the single self-edge piece. -/
theorem seg_selfA (dt : ℝ) (hdt : 0 ≤ dt) {l : ℕ} (hl : l < 1) (hv : Verd3 l)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gA) envA) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq ([((3 : ℕ), modeA 2, edgeA 2 2)].map
        (fun s => Program.ode s.2.1.sys s.2.1.dom)))
      (Formula.and (invLe gA) envA)) σ := by
  have hfa := Hmulti_window1_prefixed (fLA l) domLA gA envA aA dt htggA htgenvA []
    (by simp) (by simp) (hfLA l hl) hdomLA
    (Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA)
    (coupleA hl dt hdt hv) hσ
  simpa [modeA] using hfa

/-- The hop conversion for one static seg: the frozen-left hop run maps to the
mode's own (right-block) program over the mode domain. -/
theorem hop_conv (q : ℕ) (hq : q < 3) :
    ∀ ν μ, Program.sem ((RepoHop.mk (fRA q) (Term.const 1) domRA).prog domLA) ν μ →
      Program.sem (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA) ν μ := by
  intro ν μ h
  exact sem_ode_dom_and_right
    ((sem_rightBlock_frozen_iff (hfRA q hq) (by simp [Term.fv])).mp h)

/-- The hop list converts elementwise to the modes' own programs. -/
theorem hops_forall2 : ∀ (p : List ℕ), (∀ q ∈ p, q < 3) →
    List.Forall₂ (fun a b => ∀ ν μ, Program.sem a ν μ → Program.sem b ν μ)
      (p.map (fun q => (RepoHop.mk (fRA q) (Term.const 1) domRA).prog domLA))
      (p.map (fun q => Program.ode (rightBlock (fRA q) (Term.const 1)) domRA)) := by
  intro p
  induction p with
  | nil => exact fun _ => List.Forall₂.nil
  | cons q rest ih =>
      intro hlt4
      exact List.Forall₂.cons (hop_conv q (hlt4 q List.mem_cons_self))
        (ih (fun q' hq' => hlt4 q' (List.mem_cons_of_mem _ hq')))

/-- Non-`Hold` start `q`: static hops along the declared chain to `Hold`, then the
piece there. `path` enumerates the traversed modes (`q` first). -/
theorem seg_hopA (dt : ℝ) (hdt : 0 ≤ dt) {l : ℕ} (hl : l < 1) (hv : Verd3 l)
    (path : List ℕ) (hlt4 : ∀ q ∈ path, q < 3)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gA) envA) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq ((path.map (fun q => Program.ode (rightBlock (fRA q) (Term.const 1)) domRA))
        ++ [Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA]))
      (Formula.and (invLe gA) envA)) σ := by
  have hfa := Hmulti_window1_prefixed (fLA l) domLA gA envA aA dt htggA htgenvA
    (path.map (fun q => ⟨fRA q, Term.const 1, domRA⟩))
    (by
      intro h hh
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRA q (hlt4 q hq), by simp [Term.fv], hdomRA⟩)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
      exact static_hop_exists hσ')
    (hfLA l hl) hdomLA
    (Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA)
    (coupleA hl dt hdt hv) hσ
  rw [List.map_map] at hfa
  refine sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono ?_ ν μ hrun) hfa
  exact List.rel_append (hops_forall2 path hlt4)
    (List.Forall₂.cons (fun ν μ h => h) List.Forall₂.nil)

/-! ## The `Hmulti` provider and the gate -/

theorem HmultiA (dt : ℝ) (hdt : 0 ≤ dt) (h0 : Verd3 0) :
    ∀ P ∈ leftProgsA dt, ∀ (q : ℕ), q < GrA.modes.length → ∀ σ, σ mvA = (q : ℝ) →
      Formula.sat (Formula.and (invLe gA) envA) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrA.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrA.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gA) envA)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrA] using hq
  simp only [leftProgsA, leftDataA, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hsingle : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2))
      (b : ℕ × RMode (Var 2) × REdge (Var 2)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tg, edgeA st tg ∈ GrA.edges → st < 3 →
      GrA.modeAt st = some (modeA st) ∧ edgeA st tg ∈ GrA.edgesFrom st := by
    intro st tg he hst
    refine ⟨?_, edgeA_from he⟩
    interval_cases st <;> rfl
  rcases hP with rfl
  interval_cases q
  · exact ⟨[(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact halign 0 1 (by simp [GrA]) (by norm_num)
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 2 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg_hopA dt hdt (l := 0) (by norm_num) h0 [0, 1]
          (by intro q hq; fin_cases hq <;> norm_num) hσ
        simpa [modeA] using this)⟩
  · exact ⟨[(1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 2)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 2 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg_hopA dt hdt (l := 0) (by norm_num) h0 [1]
          (by intro q hq; fin_cases hq <;> norm_num) hσ
        simpa [modeA] using this)⟩
  · exact ⟨[(2, modeA 2, edgeA 2 2)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact halign 2 2 (by simp [GrA]) (by norm_num)),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      seg_selfA dt hdt (by norm_num) h0 hσ⟩

/-- **`robot_braking`, modal Theorem 3, UNCONDITIONAL on existence.** Two left
windows, the transition-faithful four-mode right automaton with the declared edges,
every response landing at `Hold` (static hops + one certified piece). The existence
residual is DISCHARGED (the L1 stratified route, Z3-free at the zero-field landing
mode); the only remaining hypotheses are the two per-window joint route verdicts. -/
theorem robot_braking_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (h0 : Verd3 0) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInv gA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrA mvA gA domLA domRA (leftProgsA dt)
    (canonInv gA) (encode_canonInv gA) ?_ ?_ ?_
  · exact hdis_multi GrA 0 1 dt leftDataA (by decide) httA hRvA hLA
  · exact hstep_assembled_multiE GrA mvA gA envA (leftProgsA dt) hmvgA hmvenvA
      hfreshA httA hltA (hframesA dt)
      (HmultiA dt hdt h0)
  · exact hddF_multiE GrA 0 1 dt leftDataA (canonInv gA) domLA domRA (by decide)
      httA hRvA hLA (canonInv_varsL gA hgA) (canonInv_varsR gA) hdomLA hdomRA

end RobotBrakingModal
end RelCertifier
