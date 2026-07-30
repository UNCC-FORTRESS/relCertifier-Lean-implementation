/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 (GENERATED family: mid — affine Hold landing) — `rover3tier_M1`, unconditional modal Theorem 3

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
import RelCertifier.Instances.BenchIR.rover3tier_M1
import RelCertifier.Proofs.Encoding.RepoPrefixR

namespace RelCertifier
namespace Rover3tierM1Modal

open DL DLCalTiming DLRel Parse Set

def vsA : List String := ["v", "s"]
def dummyA : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLA (l : ℕ) : Parse.PMode := rover3tier_M1_IR.L.modes.getD l dummyA
def mRA (q : ℕ) : Parse.PMode := rover3tier_M1_IR.R.modes.getD q dummyA

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
  ((Run.invToG vsA 2 ((rover3tier_M1_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-- Universal evolve: all mode evolves lower identically (kernel facts). -/
theorem domLA_univ (l : ℕ) (hl : l < 2) : hostEvolve vsA 2 Side.L (mLA l) = domLA := by
  interval_cases l <;> rfl
theorem domRA_univ (q : ℕ) (hq : q < 2) : hostEvolve vsA 2 Side.R (mRA q) = domRA := by
  interval_cases q <;> rfl

/-- The right automaton graph. -/
noncomputable def modeA (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRA q) (Term.const 1), dom := domRA, weight := 1 }

def edgeA (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

noncomputable def GrA : SearchGraph (Var 2) :=
  { modes := [modeA 0, modeA 1]
    edges := [edgeA 0 1, edgeA 0 0, edgeA 1 0, edgeA 1 1] }

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

theorem hfLA (l : ℕ) (hl : l < 2) : ∀ i, ((fLA l) i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsA) (some (mLA l))
    (by interval_cases l <;> simp [mLA, rover3tier_M1_IR, Parse.PExpr.namesFree]) i x
    (fLA_pipe l i ▸ hx))

theorem hfRA (q : ℕ) (hq : q < 2) : ∀ i, ((fRA q) i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsA) (some (mRA q))
    (by interval_cases q <;> simp [mRA, rover3tier_M1_IR, Parse.PExpr.namesFree]) i x
    (fRA_pipe q i ▸ hx))

theorem hdomLA : domLA.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsA) (some (mLA 0))
    (by simp [mLA, rover3tier_M1_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domLA_pipe ▸ hx))

theorem hdomRA : domRA.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsA) (some (mRA 0))
    (by simp [mRA, rover3tier_M1_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
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
    q < 2 ∧ m = modeA q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrA] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrA])

theorem httA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem hltA : ∀ q, ∀ e ∈ GrA.edgesFrom q, e.tgt < GrA.modes.length := by
  intro q e he
  have hmem : e ∈ GrA.edges := List.mem_of_mem_filter he
  simp only [GrA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrA, edgeA]

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
  [(fLA 0, domLA, 4), (fLA 1, domLA, 4)]

noncomputable def leftProgsA (dt : ℝ) : List (Program (Var 2)) :=
  leftDataA.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgA dt d.2.2)

theorem hLA : ∀ d ∈ leftDataA, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataA, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨hfLA 0 (by norm_num), hdomLA⟩
  · exact ⟨hfLA 1 (by norm_num), hdomLA⟩

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
  z3solve (flowQuery ⟨gA, fLA l, fRA 0, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gA, fLA l, fRA 0, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gA, fLA l, fRA 0, Term.const 1,
    Formula.and domLA domRA⟩) = Verdict.unsat

/-! ## The existence discharge — strict v-faces + non-strict s-stratum, Z3-free -/

theorem hpr2 : Run.parseRat "2" = some 2 := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpr115 : Run.parseRat "1.15" = some ((23:ℚ)/20) := by
  have h : parseQ "1.15" = some (⟨115, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  norm_num

theorem fRA0_eval0 (x : State (Var 2)) :
    Term.eval (fRA 0 0) x = 2 * (1 - x (Rv 0)) := by
  simp [fRA, hostDyn, mRA, rover3tier_M1_IR, vsA, Run.dynOf, Run.lowerE, hpr2,
    hpr10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]

theorem fRA0_eval1 (x : State (Var 2)) : Term.eval (fRA 0 1) x = x (Rv 0) := by
  simp [fRA, hostDyn, mRA, rover3tier_M1_IR, vsA, Run.dynOf, Run.lowerE, hpr2,
    hpr10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, Rv]

noncomputable def faceVLo : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceVHi : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((23:ℝ)/20))
noncomputable def faceSLo : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))

theorem faces_fv_R : ∀ gT ∈ [faceVLo, faceVHi, faceSLo], ∀ x ∈ gT.fv,
    x ∈ range Rv := by
  intro gT hgT x hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl
  · simp only [faceVLo, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨_, hx.symm⟩
  · simp only [faceVHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      Set.mem_singleton_iff] at hx
    exact ⟨_, hx.symm⟩
  · simp only [faceSLo, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨_, hx.symm⟩

theorem odeField_v (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)) x (Rv 0)
      = 2 * (1 - x (Rv 0)) := by
  have hmem : ((Rv 0, Term.binop AOp.mul (Term.const 1) (fRA 0 0)) :
      Var 2 × Term (Var 2)) ∈ jointSys (fun _ => Term.const 0) (fRA 0)
        (Term.const 1) := by
    rw [jointSys_split]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  have hb : (Rv 0 : Var 2) ∈ (jointSys (fun _ => Term.const 0) (fRA 0)
      (Term.const 1)).bound := List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [show odeField (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)) x (Rv 0)
      = ((jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)).rhs (Rv 0)).eval x
    from by simp only [odeField, if_pos hb]]
  rw [show (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)).rhs (Rv 0)
      = Term.binop AOp.mul (Term.const 1) (fRA 0 0) from
    ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hmem]
  simp [Term.eval, AOp.interp, fRA0_eval0]

theorem odeField_s (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)) x (Rv 1)
      = x (Rv 0) := by
  have hmem : ((Rv 1, Term.binop AOp.mul (Term.const 1) (fRA 0 1)) :
      Var 2 × Term (Var 2)) ∈ jointSys (fun _ => Term.const 0) (fRA 0)
        (Term.const 1) := by
    rw [jointSys_split]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩)
  have hb : (Rv 1 : Var 2) ∈ (jointSys (fun _ => Term.const 0) (fRA 0)
      (Term.const 1)).bound := List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [show odeField (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)) x (Rv 1)
      = ((jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)).rhs (Rv 1)).eval x
    from by simp only [odeField, if_pos hb]]
  rw [show (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)).rhs (Rv 1)
      = Term.binop AOp.mul (Term.const 1) (fRA 0 1) from
    ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hmem]
  simp [Term.eval, AOp.interp, fRA0_eval1]

theorem hbndS_vlo (x : State (Var 2)) (hface : Term.eval faceVLo x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1))
      (fun ω => Term.eval faceVLo ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceVLo, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceVLo ω)
      = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
    funext y
    simp [faceVLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
    odeField_v]
  norm_num [hx0]

theorem hbndS_vhi (x : State (Var 2)) (hface : Term.eval faceVHi x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1))
      (fun ω => Term.eval faceVHi ω) x < 0 := by
  have hx0 : x (Rv 0) = 23/20 := by
    simp only [faceVHi, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceVHi ω)
      = fun y => (1 : ℝ) * y (Rv 0) + (-(23/20)) := by
    funext y
    simp [faceVHi, Term.eval, AOp.interp]
    ring
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(23/20)) x,
    odeField_v]
  norm_num [hx0]

theorem hbndN_slo (x : State (Var 2)) (hcore : Term.eval faceVLo x ≤ 0) :
    Lie (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1))
      (fun ω => Term.eval faceSLo ω) x ≤ 0 := by
  have hx0 : 0 ≤ x (Rv 0) := by
    simp only [faceVLo, Term.eval, AOp.interp] at hcore
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceSLo ω)
      = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
    funext y
    simp [faceSLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 1) (-1) 0 x,
    odeField_s]
  nlinarith

theorem hLip_M (ν : State (Var 2)) :
    LipschitzOnWith 2 (odeField (jointSys (fun _ => Term.const 0) (fRA 0)
      (Term.const 1))) (Metric.closedBall ν 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x _ y _
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    rw [Real.dist_eq, odeField_v, odeField_v]
    have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
      have h := dist_le_pi_dist x y (Rv 0)
      rwa [Real.dist_eq] at h
    have hdiff : 2 * (1 - x (Rv 0)) - 2 * (1 - y (Rv 0))
        = -2 * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul]
    have : |(-2:ℝ)| = 2 := by norm_num
    rw [this]
    push_cast
    nlinarith [abs_nonneg (x (Rv 0) - y (Rv 0)), dist_nonneg (x := x) (y := y)]
  · by_cases hc1 : c = Rv 1
    · subst hc1
      rw [Real.dist_eq, odeField_s, odeField_s]
      have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
        have h := dist_le_pi_dist x y (Rv 0)
        rwa [Real.dist_eq] at h
      push_cast
      nlinarith [dist_nonneg (x := x) (y := y)]
    · have hnb : c ∉ (jointSys (fun _ => Term.const 0) (fRA 0)
          (Term.const 1)).bound ∨ True := Or.inr trivial
      by_cases hcb : c ∈ (jointSys (fun _ => Term.const 0) (fRA 0)
          (Term.const 1)).bound
      · -- bound coords are Lv j or Rv j; Rv 0/1 excluded; Lv rows are zero
        rw [Real.dist_eq]
        have hz : ∀ z : State (Var 2),
            odeField (jointSys (fun _ => Term.const 0) (fRA 0) (Term.const 1)) z c
              = 0 := by
          intro z
          obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRA 0)
              (Term.const 1), p.1 = c := by
            simpa [ODESystem.bound, List.mem_map] using hcb
          rw [show odeField (jointSys (fun _ => Term.const 0) (fRA 0)
              (Term.const 1)) z c
              = ((jointSys (fun _ => Term.const 0) (fRA 0)
                (Term.const 1)).rhs c).eval z from by
            simp only [odeField, if_pos hcb]]
          rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
          rw [jointSys_split] at hp
          rcases List.mem_append.mp hp with hp | hp
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
            simp [Term.eval]
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
            fin_cases j
            · exact absurd rfl (hfst ▸ hc0)
            · exact absurd rfl (hfst ▸ hc1)
        rw [hz x, hz y]
        simp [dist_nonneg]
      · rw [Real.dist_eq]
        simp only [odeField, if_neg hcb]
        simp [dist_nonneg]

theorem hfbnd_M (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceVLo, faceVHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fRA 0)
        (Term.const 1)) x‖ ≤ (7:NNReal) := by
  intro x hx
  have hν0 : 0 ≤ ν (Rv 0) := by
    have := hν faceVLo List.mem_cons_self
    simp only [faceVLo, Term.eval, AOp.interp] at this
    linarith
  have hν115 : ν (Rv 0) ≤ 23/20 := by
    have := hν faceVHi (by simp)
    simp only [faceVHi, Term.eval, AOp.interp] at this
    linarith
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have hνb : |ν (Rv 0)| ≤ 23/20 := abs_le.mpr ⟨by linarith, hν115⟩
  have hxb : |x (Rv 0)| ≤ 43/20 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    rw [Real.norm_eq_abs, odeField_v]
    have := abs_le.mp hxb
    rw [abs_le]
    push_cast
    constructor <;> nlinarith
  · by_cases hc1 : c = Rv 1
    · subst hc1
      rw [Real.norm_eq_abs, odeField_s]
      have := abs_le.mp hxb
      rw [abs_le]
      push_cast
      constructor <;> nlinarith
    · by_cases hcb : c ∈ (jointSys (fun _ => Term.const 0) (fRA 0)
          (Term.const 1)).bound
      · have hz : odeField (jointSys (fun _ => Term.const 0) (fRA 0)
            (Term.const 1)) x c = 0 := by
          obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fRA 0)
              (Term.const 1), p.1 = c := by
            simpa [ODESystem.bound, List.mem_map] using hcb
          rw [show odeField (jointSys (fun _ => Term.const 0) (fRA 0)
              (Term.const 1)) x c
              = ((jointSys (fun _ => Term.const 0) (fRA 0)
                (Term.const 1)).rhs c).eval x from by
            simp only [odeField, if_pos hcb]]
          rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
          rw [jointSys_split] at hp
          rcases List.mem_append.mp hp with hp | hp
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
            simp [Term.eval]
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
            fin_cases j
            · exact absurd rfl (hfst ▸ hc0)
            · exact absurd rfl (hfst ▸ hc1)
        rw [Real.norm_eq_abs, hz]
        norm_num
      · rw [Real.norm_eq_abs]
        simp only [odeField, if_neg hcb]
        norm_num

theorem hlowM : Run.lowerF vsA 2 Side.R (mRA 0).evolve =
    some (IForm.and (IForm.and
      (IForm.cmp .ge (ITerm.var (Side.R, 1)) (ITerm.rat 0))
      (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0)))
      (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat ((23:ℚ)/20)))) := by
  simp [Run.lowerF, mRA, rover3tier_M1_IR, vsA, Run.lowerE, Run.resolveVar,
    hpr00, hpr115, List.findIdx?_cons]

theorem domRA_shape : domRA = Formula.and (Formula.and
    (Formula.cmp .ge (Term.var (Side.R, 1)) (Term.const ((0:ℚ):ℝ)))
    (Formula.cmp .ge (Term.var (Side.R, 0)) (Term.const ((0:ℚ):ℝ))))
    (Formula.cmp .le (Term.var (Side.R, 0)) (Term.const (((23:ℚ)/20):ℝ))) := by
  rw [domRA_pipe]
  simp [hlowM, IForm.toHost, ITerm.toHost]

theorem esA (l : ℕ) (hl : l < 2) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, Formula.sat (Formula.and (invLe gA) envA) σ →
      HExistSegB (fLA l) (fRA 0) (Term.const 1) domLA domRA dt
        (Function.update σ tgA 0) := by
  intro σ hσ
  have hR : Formula.sat domRA σ := hσ.2.2
  rw [domRA_shape] at hR
  obtain ⟨⟨h1, h2⟩, h3⟩ := hR
  simp only [Formula.sat, CompOp.interp, Term.eval] at h1 h2 h3
  push_cast at h1 h2 h3
  have hupd0 : σ (Side.R, (0 : Fin 2)) = Function.update σ tgA 0 (Side.R, 0) := by
    rw [Function.update_of_ne (by simp [tgA, Prod.ext_iff])]
  have hupd1 : σ (Side.R, (1 : Fin 2)) = Function.update σ tgA 0 (Side.R, 1) := by
    rw [Function.update_of_ne (by simp [tgA, Prod.ext_iff])]
  have hfS : ∀ gT ∈ [faceVLo, faceVHi],
      Term.eval gT (Function.update σ tgA 0) ≤ 0 := by
    intro gT hgT
    rcases List.mem_cons.mp hgT with rfl | hgT
    · simp only [faceVLo, Term.eval, AOp.interp, Rv]
      rw [← hupd0]; linarith
    · rw [List.mem_singleton] at hgT
      subst hgT
      simp only [faceVHi, Term.eval, AOp.interp, Rv]
      rw [← hupd0]; linarith
  have hfN : ∀ gT ∈ [faceSLo],
      Term.eval gT (Function.update σ tgA 0) ≤ 0 := by
    intro gT hgT
    rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceSLo, Term.eval, AOp.interp, Rv]
    rw [← hupd1]; linarith
  refine HExistSegB_of_viability_stratified (fLA l) (fRA 0) (Term.const 1)
    domLA domRA [faceVLo, faceVHi] [] [faceSLo] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_R gT (by
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
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_R faceSLo (by simp) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x hx hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_vlo x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_vhi x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hx _
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      exact hbndN_slo x (hx faceVLo (List.mem_append_left _ List.mem_cons_self)))
    (by
      intro x hS hN
      have h0 : 0 ≤ x (Rv 0) := by
        have := hS faceVLo (List.mem_append_left _ List.mem_cons_self)
        simp only [faceVLo, Term.eval, AOp.interp] at this
        linarith
      have hv : x (Rv 0) ≤ 23/20 := by
        have := hS faceVHi (List.mem_append_left _ (by simp))
        simp only [faceVHi, Term.eval, AOp.interp] at this
        linarith
      have hs : 0 ≤ x (Rv 1) := by
        have := hN faceSLo List.mem_cons_self
        simp only [faceSLo, Term.eval, AOp.interp] at this
        linarith
      rw [domRA_shape]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
        · show CompOp.interp _ _ _
          push_cast [CompOp.interp, Term.eval]
          first
            | simpa [Rv] using hs
            | simpa [Rv] using h0
            | simpa [Rv] using hv)
    2 7 1 one_pos
    (fun ν0 _ => hLip_M ν0)
    (fun ν0 h0 => hfbnd_M ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgA 0)
    hfS
    hfN
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The per-pair bounded coupling (cert-sourced, envelope-strengthened) -/

theorem coupleA {l : ℕ} (hl : l < 2) (dt : ℝ) (hdt : 0 ≤ dt) (hv : Verd3 l) :
    ∀ σ', Formula.sat (Formula.and (invLe gA) envA) σ' → σ' tgA = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgA (leftBlock (fLA l))) domLA)
        (Program.ode (rightBlock (fRA 0) (Term.const 1)) domRA)
        (Formula.and (invLe gA) envA) tgA dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgA (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgA
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLA l) (fRA 0) (Term.const 1)
    (Formula.and domLA domRA) [gA]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, Verd3] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLA l) ++ rightBlock (fRA 0) (Term.const 1))
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
  have hbase := segment_faModalB_from_certB gA (fLA l) (fRA 0) (Term.const 1)
    domLA domRA tgA dt
    (LR_blocks_disjoint _ _ _ (hfLA l hl) (hfRA 0 (by norm_num)) (by simp [Term.fv]))
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
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRA 0) (Term.const 1) _ h
      exact aux_ne_Rv aA i hi)
    (fun h => aux_notin_range_Rv aA (rightBlock_readVars_sub (fRA 0) (Term.const 1)
      (hfRA 0 (by norm_num)) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aA (rightBlock_boundSet_sub (fRA 0) (Term.const 1) h))
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
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRA 0) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLA μ ↔ Formula.sat domLA ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Per-(window, start) responses — every response lands at `Hold` -/

/-- The satisfied-anchor update transport for the windowR coupling shape. -/
theorem coupleA' {l : ℕ} (hl : l < 2) (dt : ℝ) (hdt : 0 ≤ dt) (hv : Verd3 l) :
    ∀ σ, Formula.sat (Formula.and (invLe gA) envA) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgA (leftBlock (fLA l))) domLA)
        (Program.ode (rightBlock (fRA 0) (Term.const 1)) domRA)
        (Formula.and (invLe gA) envA) tgA dt
        (Function.update σ tgA 0) := by
  intro σ hσ
  have htgφ : tgA ∉ (Formula.and (invLe gA) envA).fv := by
    intro h
    rcases h with h | h
    · exact htggA (by simpa [invLe, Formula.fv, Term.fv] using h)
    · exact htgenvA h
  have hupdφ : Formula.sat (Formula.and (invLe gA) envA)
      (Function.update σ tgA 0) := by
    rwa [(Formula.coincidence (Formula.and (invLe gA) envA) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (invLe gA) envA) _ ↔ _)]
  exact coupleA hl dt hdt hv (Function.update σ tgA 0) hupdφ
    (Function.update_self _ _ _)

/-- The four-piece window with a hop prefix — `Hmulti_windowR_prefixed`. -/
theorem seg4A (dt : ℝ) (hdt : 0 ≤ dt) {l : ℕ} (hl : l < 2) (hv : Verd3 l)
    (path : List ℕ) (hlt2 : ∀ q ∈ path, q < 2)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gA) envA) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 4)
      (bigSeq ((path.map (fun q => Program.ode (rightBlock (fRA q) (Term.const 1))
          domRA))
        ++ List.replicate 4 (Program.ode (rightBlock (fRA 0) (Term.const 1)) domRA)))
      (Formula.and (invLe gA) envA)) σ := by
  have hfa := Hmulti_windowR_prefixed (fLA l) domLA gA envA aA dt 4 htggA htgenvA
    (path.map (fun q => ⟨fRA q, Term.const 1, domRA⟩))
    (by
      intro h hh
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRA q (hlt2 q hq), by simp [Term.fv], hdomRA⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fRA q)
        (lam := Term.const 1) (domR := domRA) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfLA l hl) hdomLA
    (List.replicate 4 (Program.ode (rightBlock (fRA 0) (Term.const 1)) domRA))
    (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ, Program.rename_refl]
      exact hdisH_progR (⟨fRA 0, Term.const 1, domRA⟩ : RepoHop 2)
        (hfRA 0 (by norm_num)) (by simp [Term.fv]) hdomRA (hfLA l hl) hdomLA)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact coupleA' hl dt hdt hv σ' hσ')
    hσ
  rw [show (path.map (fun q => (⟨fRA q, Term.const 1, domRA⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = path.map (fun q => Program.ode (rightBlock (fRA q) (Term.const 1)) domRA)
    from by rw [List.map_map]; rfl] at hfa
  exact hfa

theorem HmultiA (dt : ℝ) (hdt : 0 ≤ dt) (h0 : Verd3 0) (h1 : Verd3 1) :
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
  simp only [leftProgsA, leftDataA, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hq2 : q < 2 := by simpa [GrA] using hq
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
  have halign : ∀ st tg, edgeA st tg ∈ GrA.edges → st < 2 →
      GrA.modeAt st = some (modeA st) ∧ edgeA st tg ∈ GrA.edgesFrom st := by
    intro st tg he hst
    refine ⟨?_, edgeA_from he⟩
    interval_cases st <;> rfl
  have hlv : ∀ l, l < 2 → Verd3 l → P = windowSeg (leftBlock (fLA l)) domLA tgA dt 4 →
      True := fun _ _ _ _ => trivial
  rcases hP with rfl | rfl
  all_goals interval_cases q
  -- window 0, start 0 (landing): 4 self pieces
  · exact ⟨[(0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0),
      (0, modeA 0, edgeA 0 0)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl <;>
          exact halign 0 0 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg4A dt hdt (l := 0) (by norm_num) h0 [] (by simp) hσ
        simpa [modeA, List.replicate] using this)⟩
  -- window 0, start 1: hop [1] + 4 pieces
  · exact ⟨[(1, modeA 1, edgeA 1 0), (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0),
      (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact halign 1 0 (by simp [GrA]) (by norm_num)
        all_goals exact halign 0 0 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hsingle _))))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg4A dt hdt (l := 0) (by norm_num) h0 [1]
          (by intro q hq; fin_cases hq <;> norm_num) hσ
        simpa [modeA, List.replicate] using this)⟩
  -- window 1, start 0
  · exact ⟨[(0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0),
      (0, modeA 0, edgeA 0 0)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl <;>
          exact halign 0 0 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg4A dt hdt (l := 1) (by norm_num) h1 [] (by simp) hσ
        simpa [modeA, List.replicate] using this)⟩
  -- window 1, start 1
  · exact ⟨[(1, modeA 1, edgeA 1 0), (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0),
      (0, modeA 0, edgeA 0 0), (0, modeA 0, edgeA 0 0)],
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact halign 1 0 (by simp [GrA]) (by norm_num)
        all_goals exact halign 0 0 (by simp [GrA]) (by norm_num)),
      (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl
        (hsingle _))))),
      (fun s hs => by rw [hhead1 _ _ _ hs]),
      (by
        have := seg4A dt hdt (l := 1) (by norm_num) h1 [1]
          (by intro q hq; fin_cases hq <;> norm_num) hσ
        simpa [modeA, List.replicate] using this)⟩

/-- **`rover3tier_M1`, modal Theorem 3, UNCONDITIONAL on existence.** Two left
windows, the transition-faithful four-mode right automaton with the declared edges,
every response landing at `Hold` (static hops + one certified piece). The existence
residual is DISCHARGED (the L1 stratified route, Z3-free at the zero-field landing
mode); the only remaining hypotheses are the two per-window joint route verdicts. -/
theorem rover3tier_M1_modal (dt : ℝ) (hdt : 0 ≤ dt)
    (h0 : Verd3 0) (h1 : Verd3 1) :
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
      (HmultiA dt hdt h0 h1)
  · exact hddF_multiE GrA 0 1 dt leftDataA (canonInv gA) domLA domRA (by decide)
      httA hRvA hLA (canonInv_varsL gA hgA) (canonInv_varsR gA) hdomLA hdomRA

end Rover3tierM1Modal
end RelCertifier
