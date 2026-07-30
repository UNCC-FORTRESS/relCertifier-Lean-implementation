/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_chain_rung2`, modal Theorem 3 (the asymmetric-rate switch)

The last switch benchmark: the 4-mode Hold-terminating left envelope
(0.5 / 0.35 / 0.2 / 0) against the 3-mode right envelope (Fast 0.5 / Slow 0.3 /
Return −0.2), tolerance `θ_L ≤ θ_R + 0.30`, per-window stretch λ = 7/4, 5/4, 1, 1
and budgets k = 2, 2, 1, 1. Every window lands `ApproachSlow`.

The split here is ASYMMETRIC: the landing rate `cA = 0.3·λ` differs from the
Return rate `cB = 0.2·λ`, so the B-first fraction is `θ = 3/5` — then
`s₂ = (2/3)·s₁` and the rise `cA·s₂ = cB·s₁` cancels the drop exactly. The
pre-L3′ measurement needed a banded θ-family here; under the drop-tracked split
the single fraction closes all four windows at `dt ≤ 1/5` (worst budget
1.125·dt ≤ 0.225 < 0.3, in-kernel).

Residuals: four route verdicts (`VerdD l` — the `ApproachSlow` coupling per
window). Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.arm_chain_rung2

namespace RelCertifier
namespace ArmChainRung2Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsD : List String := ["theta"]
def dummyD : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLD (l : ℕ) : Parse.PMode := arm_chain_rung2_IR.L.modes.getD l dummyD
def mRD (q : ℕ) : Parse.PMode := arm_chain_rung2_IR.R.modes.getD q dummyD

abbrev mvD : Var 2 := (Side.Aux, 0)
abbrev aD : Fin 2 := (1 : Fin 2)
abbrev tgD : Var 2 := (Side.Aux, aD)

/-- Per-window stretch: `7/4`, `5/4`, `1`, `1`. -/
noncomputable def lamD (l : ℕ) : ℝ :=
  if l = 0 then 7/4 else if l = 1 then 5/4 else 1
/-- Landing (`ApproachSlow`) λ-stretched rate `0.3·λ`. -/
noncomputable def cAD (l : ℕ) : ℝ := 3/10 * lamD l
/-- `Return` λ-stretched rate `0.2·λ`. -/
noncomputable def cBD (l : ℕ) : ℝ := 1/5 * lamD l
/-- Per-window left rate: `1/2`, `7/20`, `1/5`, `0`. -/
noncomputable def rLD (l : ℕ) : ℝ :=
  if l = 0 then 1/2 else if l = 1 then 7/20 else if l = 2 then 1/5 else 0
/-- Per-window budget. -/
def kD (l : ℕ) : ℕ := if l ≤ 1 then 2 else 1

theorem lamD_pos (l : ℕ) : 0 < lamD l := by
  unfold lamD
  split <;> [norm_num; skip]
  split <;> norm_num

theorem lamD_bounds (l : ℕ) (hl : l < 4) : 1 ≤ lamD l ∧ lamD l ≤ 7/4 := by
  interval_cases l <;> norm_num [lamD]

noncomputable def fLD (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.L (mLD l)
noncomputable def fRD (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsD 2 Side.R (mRD q)
noncomputable def domLD : Formula (Var 2) := hostEvolve vsD 2 Side.L (mLD 0)
noncomputable def domRD : Formula (Var 2) := hostEvolve vsD 2 Side.R (mRD 0)
noncomputable def envD : Formula (Var 2) := Formula.and domLD domRD

noncomputable def gD : Term (Var 2) :=
  ((Run.invToG vsD 2 ((arm_chain_rung2_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLD_pipe (l : ℕ) (i : Fin 2) : fLD l i =
    (((some (mLD l)).bind (Run.dynOf vsD 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRD_pipe (q : ℕ) (i : Fin 2) : fRD q i =
    (((some (mRD q)).bind (Run.dynOf vsD 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLD_pipe : domLD =
    (((some (mLD 0)).bind (fun m => Run.lowerF vsD 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRD_pipe : domRD =
    (((some (mRD 0)).bind (fun m => Run.lowerF vsD 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLD (l : ℕ) (hl : l < 4) : ∀ i, (fLD l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsD) (some (mLD l))
    (by interval_cases l <;>
      simp [mLD, arm_chain_rung2_IR, Parse.PExpr.namesFree]) i x (fLD_pipe l i ▸ hx))

theorem hfRD (q : ℕ) (hq : q < 3) : ∀ i, (fRD q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsD) (some (mRD q))
    (by interval_cases q <;>
      simp [mRD, arm_chain_rung2_IR, Parse.PExpr.namesFree]) i x (fRD_pipe q i ▸ hx))

theorem hdomLD : domLD.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsD) (some (mLD 0))
    (by simp [mLD, arm_chain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLD_pipe ▸ hx))

theorem hdomRD : domRD.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsD) (some (mRD 0))
    (by simp [mRD, arm_chain_rung2_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRD_pipe ▸ hx))

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

/-! ## The right graph -/

noncomputable def modeD (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRD q) (Term.const 1), dom := domRD, weight := 1 }

def edgeD (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrD : SearchGraph (Var 2) :=
  { modes := [modeD 0, modeD 1, modeD 2],
    edges := [edgeD 0 1, edgeD 0 0, edgeD 1 2, edgeD 1 1, edgeD 2 1, edgeD 2 2] }

theorem GrD_modeAt (q : ℕ) (hq : q < 3) : GrD.modeAt q = some (modeD q) := by
  interval_cases q <;> rfl

theorem httD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltD : ∀ q, ∀ e ∈ GrD.edgesFrom q, e.tgt < GrD.modes.length := by
  intro q e he
  have hmem : e ∈ GrD.edges := List.mem_of_mem_filter he
  simp only [GrD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [GrD, edgeD]

theorem hRvD : ∀ q m, GrD.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeD q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrD] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrD])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRD q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRD q) (Term.const 1) (hfRD q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRD hy

theorem edgeD_mem : ∀ st tgt, edgeD st tgt ∈ GrD.edges →
    edgeD st tgt ∈ GrD.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeD]⟩

theorem hfreshD : ∀ q m, GrD.modeAt q = some m →
    mvD ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvD q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family -/

noncomputable def leftDataD : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLD 0, domLD, 2), (fLD 1, domLD, 2), (fLD 2, domLD, 1), (fLD 3, domLD, 1)]

noncomputable def leftProgsD (dt : ℝ) : List (Program (Var 2)) :=
  leftDataD.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgD dt d.2.2)

theorem hLD : ∀ d ∈ leftDataD, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataD, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨hfLD 0 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 1 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 2 (by norm_num), hdomLD⟩
  · exact ⟨hfLD 3 (by norm_num), hdomLD⟩

theorem hframesD (dt : ℝ) : ∀ P ∈ leftProgsD dt, FramesMv P mvD := by
  intro P hP
  simp only [leftProgsD, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgD dt d.2.2 mvD (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins and field/shape pins -/

theorem hd02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd035 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hd0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hd10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fLD0_eval (l : ℕ) (hl : l < 4) (x : State (Var 2)) :
    Term.eval (fLD l 0) x = rLD l := by
  interval_cases l <;>
    simp [fLD, hostDyn, mLD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd035, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, rLD]

theorem fRD0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fRD q 0) x =
      (if q = 0 then (1:ℝ)/2 else if q = 1 then 3/10 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRD, hostDyn, mRD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd03, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRD1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fRD q 1) x = 0 := by
  interval_cases q <;>
    simp [fRD, hostDyn, mRD, arm_chain_rung2_IR, vsD, Run.dynOf, Run.lowerE,
      hd05, hd03, hd02, hd0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRD (x : State (Var 2)) : Formula.sat domRD x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRD, hostEvolve, mRD, arm_chain_rung2_IR, vsD]
  simp [Run.lowerF, Run.lowerE, hd00, hd10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_domLD (x : State (Var 2)) : Formula.sat domLD x ↔
    (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1) := by
  simp only [domLD, hostEvolve, mLD, arm_chain_rung2_IR, vsD]
  simp [Run.lowerF, Run.lowerE, hd00, hd10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem gD_eval (x : State (Var 2)) :
    Term.eval gD x = x (Lv 0) - (x (Rv 0) + 3/10) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gD, arm_chain_rung2_IR, Run.invToG, Run.lowerE, vsD, hd030,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

end ArmChainRung2Modal
end RelCertifier