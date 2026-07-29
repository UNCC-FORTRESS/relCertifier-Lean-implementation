/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_chain_rung1`, modal Theorem 3 (switch, per-window λ and k)

The second switch shape: a 3-mode piecewise-rate left envelope (`ApproachFast
θ' = 0.5`, `ApproachSlow θ' = 0.3`, `Return θ' = −0.2`) against the coarse 2-mode
right envelope of the pilot, tolerance `θ_L ≤ θ_R + 0.4`, with PER-WINDOW stretch
and budget: λ = 5/2, k = 3 (Fast); λ = 3/2, k = 2 (Slow); λ = 1, k = 1 (Return).

Every window lands `Approach` (the cover certifies it for all three), so the
pilot's dichotomy transfers with the per-window rate `r_l = λ_l/5`: far anchors
(`θ_R ≤ 1 − r_l·dt`) ride `Approach` alone; near-ceiling anchors take the
drop-tracked B-first split at θ = 1/2 (`cA = cB = r_l`). One variable (`theta`),
padded to `n = 2`; the left fields are constants, so every witness is a line.
dt-capped at 1/5 as in the pilot.

Residuals: three route verdicts (`VerdC l` — the `Approach` coupling per window).
Axioms: the standard three + `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Instances.BenchIR.arm_chain_rung1

namespace RelCertifier
namespace ArmChainRung1Modal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsC : List String := ["theta"]
def dummyC : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLC (l : ℕ) : Parse.PMode := arm_chain_rung1_IR.L.modes.getD l dummyC
def mRC (q : ℕ) : Parse.PMode := arm_chain_rung1_IR.R.modes.getD q dummyC

abbrev mvC : Var 2 := (Side.Aux, 0)
abbrev aC : Fin 2 := (1 : Fin 2)
abbrev tgC : Var 2 := (Side.Aux, aC)

/-- Per-window stretch: `5/2`, `3/2`, `1`. -/
noncomputable def lamC (l : ℕ) : ℝ := if l = 0 then 5/2 else if l = 1 then 3/2 else 1
/-- Per-window λ-stretched right rate `λ_l/5`. -/
noncomputable def rC (l : ℕ) : ℝ := lamC l / 5
/-- Per-window left rate: `1/2`, `3/10`, `−1/5`. -/
noncomputable def rLC (l : ℕ) : ℝ := if l = 0 then 1/2 else if l = 1 then 3/10 else -(1/5)
/-- Per-window budget. -/
def kC (l : ℕ) : ℕ := if l = 0 then 3 else if l = 1 then 2 else 1

theorem lamC_pos (l : ℕ) : 0 < lamC l := by
  unfold lamC
  split <;> [norm_num; skip]
  split <;> norm_num

theorem rC_bounds (l : ℕ) (hl : l < 3) : 1/5 ≤ rC l ∧ rC l ≤ 1/2 := by
  interval_cases l <;> norm_num [rC, lamC]

noncomputable def fLC (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsC 2 Side.L (mLC l)
noncomputable def fRC (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsC 2 Side.R (mRC q)
noncomputable def domLC : Formula (Var 2) := hostEvolve vsC 2 Side.L (mLC 0)
noncomputable def domRC : Formula (Var 2) := hostEvolve vsC 2 Side.R (mRC 0)
noncomputable def envC : Formula (Var 2) := Formula.and domLC domRC

noncomputable def gC : Term (Var 2) :=
  ((Run.invToG vsC 2 ((arm_chain_rung1_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLC_pipe (l : ℕ) (i : Fin 2) : fLC l i =
    (((some (mLC l)).bind (Run.dynOf vsC 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRC_pipe (q : ℕ) (i : Fin 2) : fRC q i =
    (((some (mRC q)).bind (Run.dynOf vsC 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLC_pipe : domLC =
    (((some (mLC 0)).bind (fun m => Run.lowerF vsC 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRC_pipe : domRC =
    (((some (mRC 0)).bind (fun m => Run.lowerF vsC 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLC (l : ℕ) (hl : l < 3) : ∀ i, (fLC l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsC) (some (mLC l))
    (by interval_cases l <;>
      simp [mLC, arm_chain_rung1_IR, Parse.PExpr.namesFree]) i x (fLC_pipe l i ▸ hx))

theorem hfRC (q : ℕ) (hq : q < 2) : ∀ i, (fRC q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsC) (some (mRC q))
    (by interval_cases q <;>
      simp [mRC, arm_chain_rung1_IR, Parse.PExpr.namesFree]) i x (fRC_pipe q i ▸ hx))

theorem hdomLC : domLC.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsC) (some (mLC 0))
    (by simp [mLC, arm_chain_rung1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLC_pipe ▸ hx))

theorem hdomRC : domRC.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsC) (some (mRC 0))
    (by simp [mRC, arm_chain_rung1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRC_pipe ▸ hx))

theorem hgC : gC.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgC : mvC ∉ gC.fv := fun h => by
  rcases hgC h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggC : tgC ∉ gC.fv := fun h => by
  rcases hgC h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvC : mvC ∉ envC.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvC : tgC ∉ envC.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (the REAL λ = 1 automaton) -/

noncomputable def modeC (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRC q) (Term.const 1), dom := domRC, weight := 1 }

def edgeC (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrC : SearchGraph (Var 2) :=
  { modes := [modeC 0, modeC 1],
    edges := [edgeC 0 1, edgeC 0 0, edgeC 1 0, edgeC 1 1] }

theorem GrC_modeAt (q : ℕ) (hq : q < 2) : GrC.modeAt q = some (modeC q) := by
  interval_cases q <;> rfl

theorem httC : ∀ q, ∀ e ∈ GrC.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrC.edges := List.mem_of_mem_filter he
  simp only [GrC, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem hltC : ∀ q, ∀ e ∈ GrC.edgesFrom q, e.tgt < GrC.modes.length := by
  intro q e he
  have hmem : e ∈ GrC.edges := List.mem_of_mem_filter he
  simp only [GrC, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrC, edgeC]

theorem hRvC : ∀ q m, GrC.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeC q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrC] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrC])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRC q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRC q) (Term.const 1) (hfRC q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRC hy

theorem edgeC_mem : ∀ st tgt, edgeC st tgt ∈ GrC.edges →
    edgeC st tgt ∈ GrC.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeC]⟩

theorem hfreshC : ∀ q m, GrC.modeAt q = some m →
    mvC ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvC q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family (per-window budgets) -/

noncomputable def leftDataC : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLC 0, domLC, 3), (fLC 1, domLC, 2), (fLC 2, domLC, 1)]

noncomputable def leftProgsC (dt : ℝ) : List (Program (Var 2)) :=
  leftDataC.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgC dt d.2.2)

theorem hLC : ∀ d ∈ leftDataC, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataC, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLC 0 (by norm_num), hdomLC⟩
  · exact ⟨hfLC 1 (by norm_num), hdomLC⟩
  · exact ⟨hfLC 2 (by norm_num), hdomLC⟩

theorem hframesC (dt : ℝ) : ∀ P ∈ leftProgsC dt, FramesMv P mvC := by
  intro P hP
  simp only [leftProgsC, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgC dt d.2.2 mvC (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hc02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hc05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hc03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hc04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

theorem fLC0_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fLC l 0) x = rLC l := by
  interval_cases l <;>
    simp [fLC, hostDyn, mLC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc05, hc03, hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, rLC]

theorem fRC0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRC q 0) x = (if q = 0 then (1:ℝ)/5 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRC, hostDyn, mRC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRC1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRC q 1) x = 0 := by
  interval_cases q <;>
    simp [fRC, hostDyn, mRC, arm_chain_rung1_IR, vsC, Run.dynOf, Run.lowerE,
      hc02, hc0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domRC (x : State (Var 2)) : Formula.sat domRC x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRC, hostEvolve, mRC, arm_chain_rung1_IR, vsC]
  simp [Run.lowerF, Run.lowerE, hc00, hc10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_domLC (x : State (Var 2)) : Formula.sat domLC x ↔
    (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1) := by
  simp only [domLC, hostEvolve, mLC, arm_chain_rung1_IR, vsC]
  simp [Run.lowerF, Run.lowerE, hc00, hc10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem gC_eval (x : State (Var 2)) :
    Term.eval gC x = x (Lv 0) - (x (Rv 0) + 2/5) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gC, arm_chain_rung1_IR, Run.invToG, Run.lowerE, vsC, hc04,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

end ArmChainRung1Modal
end RelCertifier