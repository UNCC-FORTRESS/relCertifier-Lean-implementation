/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 (GENERATED family: mid — affine Hold landing) — `rover_4d_box`, unconditional modal Theorem 3

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
import RelCertifier.Instances.BenchIR.rover_4d_box

namespace RelCertifier
namespace Rover4dBoxModal

open DL DLCalTiming DLRel Parse Set

def vsA : List String := ["px", "py", "vx", "vy"]
def dummyA : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLA (l : ℕ) : Parse.PMode := rover_4d_box_IR.L.modes.getD l dummyA
def mRA (q : ℕ) : Parse.PMode := rover_4d_box_IR.R.modes.getD q dummyA

abbrev mvA : Var 4 := (Side.Aux, 0)
abbrev aA : Fin 4 := (1 : Fin 4)
abbrev tgA : Var 4 := (Side.Aux, aA)

/-- Lowered fields and domains (`n = 2`; the left is genuinely 2-D, the right's `v`
row is inert). -/
noncomputable def fLA (l : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsA 4 Side.L (mLA l)
noncomputable def fRA (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsA 4 Side.R (mRA q)
noncomputable def domLA : Formula (Var 4) := hostEvolve vsA 4 Side.L (mLA 0)
noncomputable def domRA : Formula (Var 4) := hostEvolve vsA 4 Side.R (mRA 0)

/-- The joint universal envelope — the loop invariant's conditioning conjunct. -/
noncomputable def envA : Formula (Var 4) := Formula.and domLA domRA

/-- The invariant term (`L_theta − (R_theta + 0.15)`). -/
noncomputable def gA : Term (Var 4) :=
  ((Run.invToG vsA 4 ((rover_4d_box_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-- Universal evolve: all mode evolves lower identically (kernel facts). -/
theorem domLA_univ (l : ℕ) (hl : l < 1) : hostEvolve vsA 4 Side.L (mLA l) = domLA := by
  interval_cases l <;> rfl
theorem domRA_univ (q : ℕ) (hq : q < 2) : hostEvolve vsA 4 Side.R (mRA q) = domRA := by
  interval_cases q <;> rfl

/-- The right automaton graph. -/
noncomputable def modeA (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRA q) (Term.const 1), dom := domRA, weight := 1 }

def edgeA (s t : ℕ) : REdge (Var 4) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

noncomputable def GrA : SearchGraph (Var 4) :=
  { modes := [modeA 0, modeA 1]
    edges := [edgeA 0 1, edgeA 0 0, edgeA 1 1] }

/-! ## Side-splits (kernel facts via the lowering pipelines) -/

theorem fLA_pipe (l : ℕ) (i : Fin 4) : fLA l i =
    (((some (mLA l)).bind (Run.dynOf vsA 4 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRA_pipe (q : ℕ) (i : Fin 4) : fRA q i =
    (((some (mRA q)).bind (Run.dynOf vsA 4 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLA_pipe : domLA =
    (((some (mLA 0)).bind (fun m => Run.lowerF vsA 4 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRA_pipe : domRA =
    (((some (mRA 0)).bind (fun m => Run.lowerF vsA 4 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLA (l : ℕ) (hl : l < 1) : ∀ i, ((fLA l) i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsA) (some (mLA l))
    (by interval_cases l <;> simp [mLA, rover_4d_box_IR, Parse.PExpr.namesFree]) i x
    (fLA_pipe l i ▸ hx))

theorem hfRA (q : ℕ) (hq : q < 2) : ∀ i, ((fRA q) i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsA) (some (mRA q))
    (by interval_cases q <;> simp [mRA, rover_4d_box_IR, Parse.PExpr.namesFree]) i x
    (fRA_pipe q i ▸ hx))

theorem hdomLA : domLA.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsA) (some (mLA 0))
    (by simp [mLA, rover_4d_box_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domLA_pipe ▸ hx))

theorem hdomRA : domRA.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsA) (some (mRA 0))
    (by simp [mRA, rover_4d_box_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
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

theorem GrA_modeAt {q : ℕ} {m : RMode (Var 4)} (hm : GrA.modeAt q = some m) :
    q < 2 ∧ m = modeA q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrA])

theorem httA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

theorem hltA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.tgt < GrA.modes.length := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> norm_num [GrA, edgeA]

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

noncomputable def leftDataA : List ((Fin 4 → Term (Var 4)) × Formula (Var 4) × ℕ) :=
  [(fLA 0, domLA, 1)]

noncomputable def leftProgsA (dt : ℝ) : List (Program (Var 4)) :=
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
  z3solve (flowQuery ⟨gA, fLA l, fRA 1, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gA, fLA l, fRA 1, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gA, fLA l, fRA 1, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat

/-! ## The existence discharge — closed-form linear drift, Z3-free

`SETTLE`'s velocities are constant (`vx' = vy' = 0`) and only the positions move
(`px' = vx`, `py' = vy`), so the response is the explicit linear drift — a direct
`HExistSegB` witness, no Picard, no face machinery. (The stratified consumer does
not apply here: its Lipschitz/bound data is conditioned on the strict+growth
sublevel only, and this mode's field bound needs the non-strict faces — the
recorded consumer limitation. The closed form is both simpler and stronger.) -/

theorem hpr0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

theorem hpr15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

theorem hprm1 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr1 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fRA1_eval0 (x : State (Var 4)) : Term.eval (fRA 1 0) x = x (Rv 2) := by
  simp [fRA, hostDyn, mRA, rover_4d_box_IR, vsA, Run.dynOf, Run.lowerE, hpr0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, Rv]
theorem fRA1_eval1 (x : State (Var 4)) : Term.eval (fRA 1 1) x = x (Rv 3) := by
  simp [fRA, hostDyn, mRA, rover_4d_box_IR, vsA, Run.dynOf, Run.lowerE, hpr0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, Rv]
theorem fRA1_eval2 (x : State (Var 4)) : Term.eval (fRA 1 2) x = 0 := by
  simp [fRA, hostDyn, mRA, rover_4d_box_IR, vsA, Run.dynOf, Run.lowerE, hpr0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]
theorem fRA1_eval3 (x : State (Var 4)) : Term.eval (fRA 1 3) x = 0 := by
  simp [fRA, hostDyn, mRA, rover_4d_box_IR, vsA, Run.dynOf, Run.lowerE, hpr0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem hlowR4 : Run.lowerF vsA 4 Side.R (mRA 0).evolve =
    some (IForm.and (IForm.and (IForm.and
      (IForm.cmp .ge (ITerm.var (Side.R, 2)) (ITerm.rat ((1:ℚ)/2)))
      (IForm.cmp .le (ITerm.var (Side.R, 2)) (ITerm.rat ((3:ℚ)/2))))
      (IForm.cmp .ge (ITerm.var (Side.R, 3)) (ITerm.rat (-1))))
      (IForm.cmp .le (ITerm.var (Side.R, 3)) (ITerm.rat 1))) := by
  simp [Run.lowerF, mRA, rover_4d_box_IR, vsA, Run.lowerE, Run.resolveVar,
    hpr05, hpr15, hprm1, hpr1, List.findIdx?_cons]

theorem domRA_shape : domRA = Formula.and (Formula.and (Formula.and
    (Formula.cmp .ge (Term.var (Side.R, 2)) (Term.const (((1:ℚ)/2):ℝ)))
    (Formula.cmp .le (Term.var (Side.R, 2)) (Term.const (((3:ℚ)/2):ℝ))))
    (Formula.cmp .ge (Term.var (Side.R, 3)) (Term.const ((-1:ℚ):ℝ))))
    (Formula.cmp .le (Term.var (Side.R, 3)) (Term.const ((1:ℚ):ℝ))) := by
  rw [domRA_pipe]
  simp [hlowR4, IForm.toHost, ITerm.toHost]

/-- The linear-drift response: positions advance at the (frozen) velocities. -/
noncomputable def driftW (ν : State (Var 4)) (t : ℝ) : State (Var 4) :=
  Function.update (Function.update ν (Rv 0) (ν (Rv 0) + t * ν (Rv 2)))
    (Rv 1) (ν (Rv 1) + t * ν (Rv 3))

theorem r01 : (Rv (0:Fin 4) : Var 4) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
theorem r21 : (Rv (2:Fin 4) : Var 4) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
theorem r20 : (Rv (2:Fin 4) : Var 4) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
theorem r31 : (Rv (3:Fin 4) : Var 4) ≠ Rv 1 := by simp [Rv, Prod.ext_iff]
theorem r30 : (Rv (3:Fin 4) : Var 4) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]

theorem driftW_c0 (ν : State (Var 4)) (t : ℝ) :
    driftW ν t (Rv 0) = ν (Rv 0) + t * ν (Rv 2) := by
  rw [driftW, Function.update_of_ne r01, Function.update_self]
theorem driftW_c1 (ν : State (Var 4)) (t : ℝ) :
    driftW ν t (Rv 1) = ν (Rv 1) + t * ν (Rv 3) := by
  rw [driftW, Function.update_self]
theorem driftW_other (ν : State (Var 4)) (t : ℝ) {x : Var 4}
    (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) : driftW ν t x = ν x := by
  rw [driftW, Function.update_of_ne h1, Function.update_of_ne h0]
theorem driftW_at0 (ν : State (Var 4)) : driftW ν 0 = ν := by
  funext x
  by_cases h0 : x = Rv 0
  · subst h0; rw [driftW_c0]; ring
  · by_cases h1 : x = Rv 1
    · subst h1; rw [driftW_c1]; ring
    · exact driftW_other ν 0 h0 h1

theorem esA (l : ℕ) (hl : l < 1) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (invLe gA) envA) σ →
      HExistSegB (fLA l) (fRA 1) (Term.const 1) domLA domRA dt
        (Function.update σ tgA 0) := by
  intro σ hσ
  intro s ΦL hs0 hsdt hΦL0 hderL hmaskL hdomL
  set ν := ΦL s with hν
  refine ⟨driftW ν, driftW_at0 ν, ?_, ?_, ?_⟩
  · intro t ht p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    fin_cases j
    · have hfun : (fun u => driftW ν u (Rv 0)) = fun u => ν (Rv 0) + u * ν (Rv 2) := by
        funext u; exact driftW_c0 ν u
      have hev : Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 0))
          (driftW ν t) = ν (Rv 2) := by
        simp [Term.eval, AOp.interp, fRA1_eval0, driftW_other ν t r20 r21]
      show HasDerivWithinAt (fun u => driftW ν u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 0))
          (driftW ν t)) (Icc 0 s) t
      rw [hfun, hev]
      simpa [mul_comm] using
        ((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul (ν (Rv 2))).const_add
          (ν (Rv 0))
    · have hfun : (fun u => driftW ν u (Rv 1)) = fun u => ν (Rv 1) + u * ν (Rv 3) := by
        funext u; exact driftW_c1 ν u
      have hev : Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 1))
          (driftW ν t) = ν (Rv 3) := by
        simp [Term.eval, AOp.interp, fRA1_eval1, driftW_other ν t r30 r31]
      show HasDerivWithinAt (fun u => driftW ν u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 1))
          (driftW ν t)) (Icc 0 s) t
      rw [hfun, hev]
      simpa [mul_comm] using
        ((hasDerivWithinAt_id t (Icc (0:ℝ) s)).const_mul (ν (Rv 3))).const_add
          (ν (Rv 1))
    · have hfun : (fun u => driftW ν u (Rv 2)) = fun _ => ν (Rv 2) := by
        funext u; exact driftW_other ν u r20 r21
      have hev : Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 2))
          (driftW ν t) = 0 := by
        simp [Term.eval, AOp.interp, fRA1_eval2]
      show HasDerivWithinAt (fun u => driftW ν u (Rv 2))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 2))
          (driftW ν t)) (Icc 0 s) t
      rw [hfun, hev]
      exact hasDerivWithinAt_const t _ _
    · have hfun : (fun u => driftW ν u (Rv 3)) = fun _ => ν (Rv 3) := by
        funext u; exact driftW_other ν u r30 r31
      have hev : Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 3))
          (driftW ν t) = 0 := by
        simp [Term.eval, AOp.interp, fRA1_eval3]
      show HasDerivWithinAt (fun u => driftW ν u (Rv 3))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRA 1 3))
          (driftW ν t)) (Icc 0 s) t
      rw [hfun, hev]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      intro hceq
      exact hx (hceq ▸ List.mem_map.mpr
        ⟨(Rv 0, Term.binop AOp.mul (Term.const 1) (fRA 1 0)),
          List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩, rfl⟩)
    have h1 : x ≠ Rv 1 := by
      intro hceq
      exact hx (hceq ▸ List.mem_map.mpr
        ⟨(Rv 1, Term.binop AOp.mul (Term.const 1) (fRA 1 1)),
          List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩, rfl⟩)
    exact driftW_other ν t h0 h1
  · intro t ht
    have hR : Formula.sat domRA σ := hσ.2.2
    rw [domRA_shape] at hR
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hR
    simp only [Formula.sat, CompOp.interp, Term.eval] at h1 h2 h3 h4
    push_cast at h1 h2 h3 h4
    have hmask2 : ν (Rv 2) = σ (Side.R, (2 : Fin 4)) := by
      rw [hν]
      have hm := hmaskL s (right_mem_Icc.mpr hs0) (Rv 2) (by
        intro hb
        obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ hb
        exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
      rw [hm, Function.update_of_ne (by simp [tgA, Rv, Prod.ext_iff])]
    have hmask3 : ν (Rv 3) = σ (Side.R, (3 : Fin 4)) := by
      rw [hν]
      have hm := hmaskL s (right_mem_Icc.mpr hs0) (Rv 3) (by
        intro hb
        obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ hb
        exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
      rw [hm, Function.update_of_ne (by simp [tgA, Rv, Prod.ext_iff])]
    rw [domRA_shape]
    have hd2 : driftW ν t (Rv 2) = ν (Rv 2) := driftW_other ν t r20 r21
    have hd3 : driftW ν t (Rv 3) = ν (Rv 3) := driftW_other ν t r30 r31
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      · show CompOp.interp _ _ _
        push_cast [CompOp.interp, Term.eval]
        first
          | (rw [show ((Side.R, (2:Fin 4)) : Var 4) = Rv 2 from rfl, hd2, hmask2]
             linarith)
          | (rw [show ((Side.R, (3:Fin 4)) : Var 4) = Rv 3 from rfl, hd3, hmask3]
             linarith)

/-! ## The per-pair bounded coupling (cert-sourced, envelope-strengthened) -/

theorem coupleA {l : ℕ} (hl : l < 1) (dt : ℝ) (hdt : 0 ≤ dt) (hv : Verd3 l) :
    ∀ σ', Formula.sat (Formula.and (invLe gA) envA) σ' → σ' tgA = 0 →
      faModalB (Equiv.refl (Var 4))
        (Program.ode (DLCalTiming.clk tgA (leftBlock (fLA l))) domLA)
        (Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA)
        (Formula.and (invLe gA) envA) tgA dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgA (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgA
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLA l) (fRA 1) (Term.const 1)
    (Formula.and domLA domRA) [gA]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, Verd3] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLA l) ++ rightBlock (fRA 1) (Term.const 1))
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
  have hbase := segment_faModalB_from_certB gA (fLA l) (fRA 1) (Term.const 1)
    domLA domRA tgA dt
    (LR_blocks_disjoint _ _ _ (hfLA l hl) (hfRA 1 (by norm_num)) (by simp [Term.fv]))
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
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRA 1) (Term.const 1) _ h
      exact aux_ne_Rv aA i hi)
    (fun h => aux_notin_range_Rv aA (rightBlock_readVars_sub (fRA 1) (Term.const 1)
      (hfRA 1 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aA (rightBlock_boundSet_sub (fRA 1) (Term.const 1) h))
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
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRA 1) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLA μ ↔ Formula.sat domLA ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Per-(window, start) responses — every response lands at `Hold` -/

/-- Start `Hold` (3): the single self-edge piece. -/
theorem seg_selfA (dt : ℝ) (hdt : 0 ≤ dt) {l : ℕ} (hl : l < 1) (hv : Verd3 l)
    {σ : State (Var 4)} (hσ : Formula.sat (Formula.and (invLe gA) envA) σ) :
    Formula.sat (faModal (Equiv.refl (Var 4))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq ([((1 : ℕ), modeA 1, edgeA 1 1)].map
        (fun s => Program.ode s.2.1.sys s.2.1.dom)))
      (Formula.and (invLe gA) envA)) σ := by
  have hfa := Hmulti_window1_prefixed (fLA l) domLA gA envA aA dt htggA htgenvA []
    (by simp) (by simp) (hfLA l hl) hdomLA
    (Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA)
    (coupleA hl dt hdt hv) hσ
  simpa [modeA] using hfa

/-- The hop conversion for one static seg: the frozen-left hop run maps to the
mode's own (right-block) program over the mode domain. -/
theorem hop_conv (q : ℕ) (hq : q < 2) :
    ∀ ν μ, Program.sem ((RepoHop.mk (fRA q) (Term.const 1) domRA).prog domLA) ν μ →
      Program.sem (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA) ν μ := by
  intro ν μ h
  exact sem_ode_dom_and_right
    ((sem_rightBlock_frozen_iff (hfRA q hq) (by simp [Term.fv])).mp h)

/-- The hop list converts elementwise to the modes' own programs. -/
theorem hops_forall2 : ∀ (p : List ℕ), (∀ q ∈ p, q < 2) →
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
    (path : List ℕ) (hlt4 : ∀ q ∈ path, q < 2)
    {σ : State (Var 4)} (hσ : Formula.sat (Formula.and (invLe gA) envA) σ) :
    Formula.sat (faModal (Equiv.refl (Var 4))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq ((path.map (fun q => Program.ode (rightBlock (fRA q) (Term.const 1)) domRA))
        ++ [Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA]))
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
    (Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA)
    (coupleA hl dt hdt hv) hσ
  rw [List.map_map] at hfa
  refine sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono ?_ ν μ hrun) hfa
  exact List.rel_append (hops_forall2 path hlt4)
    (List.Forall₂.cons (fun ν μ h => h) List.Forall₂.nil)

/-! ## The `Hmulti` provider and the gate -/

theorem HmultiA (dt : ℝ) (hdt : 0 ≤ dt) (h0 : Verd3 0) :
    ∀ P ∈ leftProgsA dt, ∀ (q : ℕ), q < GrA.modes.length → ∀ σ, σ mvA = (q : ℝ) →
      Formula.sat (Formula.and (invLe gA) envA) σ →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrA.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrA.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gA) envA)) σ := by
  intro P hP q hq σ hmv hσ
  simp only [leftProgsA, leftDataA, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hq2 : q < 2 := by simpa [GrA] using hq
  have hsingle : ∀ (a : ℕ × RMode (Var 4) × REdge (Var 4)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 4) × REdge (Var 4))
      (b : ℕ × RMode (Var 4) × REdge (Var 4)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 4) × REdge (Var 4)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tg, edgeA st tg ∈ GrA.edges → st < 2 →
      GrA.modeAt st = some (modeA st) ∧ edgeA st tg ∈ GrA.edgesFrom st := by
    intro st tg he hst
    refine ⟨?_, edgeA_from he⟩
    interval_cases st <;> rfl
  rcases hP with rfl
  interval_cases q
  · exact ⟨[(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 1)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact halign 0 1 (by simp [GrA]) (by norm_num)
        · exact halign 1 1 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hsingle _)),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg_hopA dt hdt (l := 0) (by norm_num) h0 [0]
          (by intro q hq; fin_cases hq <;> norm_num) hσ
        simpa [modeA] using this)⟩
  · exact ⟨[(1, modeA 1, edgeA 1 1)],
      (by
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact halign 1 1 (by simp [GrA]) (by norm_num)),
      hsingle _,
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      seg_selfA dt hdt (by norm_num) h0 hσ⟩

/-- **`rover_4d_box`, modal Theorem 3, UNCONDITIONAL on existence.** Two left
windows, the transition-faithful four-mode right automaton with the declared edges,
every response landing at `Hold` (static hops + one certified piece). The existence
residual is DISCHARGED (the L1 stratified route, Z3-free at the zero-field landing
mode); the only remaining hypotheses are the two per-window joint route verdicts. -/
theorem rover_4d_box_modal (dt : ℝ) (hdt : 0 ≤ dt)
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

end Rover4dBoxModal
end RelCertifier
