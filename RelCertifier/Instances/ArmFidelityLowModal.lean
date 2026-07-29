/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# T3-6 — `arm_fidelity_low`, modal Theorem 3 (the L3 switch pilot)

The first intra-piece-switch instance. The PD arm (left, `θ' = v`,
`v' = −(θ − 0.5) − 2v`) refines a coarse two-mode constant-rate envelope (right,
`Approach θ' = +0.2`, `Return θ' = −0.2`) at tolerance `θ_L ≤ θ_R + 0.4`, coupled at
`λ = 5` with `k = 5` windows.

The landing mode is `Approach` for both windows, but an `Approach` response would
exit the right envelope (`θ_R ≤ 1`) mid-piece from near-ceiling anchors. Per piece
the response is the drop-tracked B-first split (L3′): from anchors with face room
(`θ_R ≤ 1 − dt`, at the λ-stretched rate `cA·λ = 1`) run `Approach` alone; from
near-ceiling anchors run `Return` for `θ = 1/2` of the piece and then `Approach` —
the rise exactly cancels the drop (`cA = cB = 0.2`), and the invariant charge
`MgB·θ·dt` is covered because near the ceiling the invariant has at least `0.4 −
dt` of slack. The dichotomy closes for `dt ≤ 1/5` — switch instances are dt-CAPPED,
unlike the dt-uniform instances landed so far.

Both split-branch phases and the A-alone branch discharge existence Z3-free (the
fields are constant-rate; explicit linear witnesses). The λ = 5 coupling converts
to the real λ = 1 automaton per piece via `sem_rightBlock_reparam` (L7's first
instantiation).

Residual: one route verdict pack (`VerdF` — the `Approach` coupling, per window).
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
import RelCertifier.Instances.BenchIR.arm_fidelity_low

namespace RelCertifier
namespace ArmFidelityLowModal

open DL DLCalTiming DLRel Parse Set

set_option maxHeartbeats 1600000

def vsF : List String := ["theta", "v"]
def dummyF : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLF (l : ℕ) : Parse.PMode := arm_fidelity_low_IR.L.modes.getD l dummyF
def mRF (q : ℕ) : Parse.PMode := arm_fidelity_low_IR.R.modes.getD q dummyF

abbrev mvF : Var 2 := (Side.Aux, 0)
abbrev aF : Fin 2 := (1 : Fin 2)
abbrev tgF : Var 2 := (Side.Aux, aF)

noncomputable def fLF (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsF 2 Side.L (mLF l)
noncomputable def fRF (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsF 2 Side.R (mRF q)
noncomputable def domLF : Formula (Var 2) := hostEvolve vsF 2 Side.L (mLF 0)
noncomputable def domRF : Formula (Var 2) := hostEvolve vsF 2 Side.R (mRF 0)
noncomputable def envF : Formula (Var 2) := Formula.and domLF domRF

noncomputable def gF : Term (Var 2) :=
  ((Run.invToG vsF 2 ((arm_fidelity_low_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## Side-splits -/

theorem fLF_pipe (l : ℕ) (i : Fin 2) : fLF l i =
    (((some (mLF l)).bind (Run.dynOf vsF 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRF_pipe (q : ℕ) (i : Fin 2) : fRF q i =
    (((some (mRF q)).bind (Run.dynOf vsF 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLF_pipe : domLF =
    (((some (mLF 0)).bind (fun m => Run.lowerF vsF 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRF_pipe : domRF =
    (((some (mRF 0)).bind (fun m => Run.lowerF vsF 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLF (l : ℕ) (hl : l < 2) : ∀ i, (fLF l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsF) (some (mLF l))
    (by interval_cases l <;>
      simp [mLF, arm_fidelity_low_IR, Parse.PExpr.namesFree]) i x (fLF_pipe l i ▸ hx))

theorem hfRF (q : ℕ) (hq : q < 2) : ∀ i, (fRF q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsF) (some (mRF q))
    (by interval_cases q <;>
      simp [mRF, arm_fidelity_low_IR, Parse.PExpr.namesFree]) i x (fRF_pipe q i ▸ hx))

theorem hdomLF : domLF.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsF) (some (mLF 0))
    (by simp [mLF, arm_fidelity_low_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLF_pipe ▸ hx))

theorem hdomRF : domRF.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsF) (some (mRF 0))
    (by simp [mRF, arm_fidelity_low_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRF_pipe ▸ hx))

theorem hgF : gF.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgF : mvF ∉ gF.fv := fun h => by
  rcases hgF h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggF : tgF ∉ gF.fv := fun h => by
  rcases hgF h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvF : mvF ∉ envF.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvF : tgF ∉ envF.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (the REAL λ = 1 automaton) -/

noncomputable def modeF (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRF q) (Term.const 1), dom := domRF, weight := 1 }

def edgeF (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrF : SearchGraph (Var 2) :=
  { modes := [modeF 0, modeF 1],
    edges := [edgeF 0 1, edgeF 0 0, edgeF 1 0, edgeF 1 1] }

theorem GrF_modeAt (q : ℕ) (hq : q < 2) : GrF.modeAt q = some (modeF q) := by
  interval_cases q <;> rfl

theorem httF : ∀ q, ∀ e ∈ GrF.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrF.edges := List.mem_of_mem_filter he
  simp only [GrF, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem hltF : ∀ q, ∀ e ∈ GrF.edgesFrom q, e.tgt < GrF.modes.length := by
  intro q e he
  have hmem : e ∈ GrF.edges := List.mem_of_mem_filter he
  simp only [GrF, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrF, edgeF]

theorem hRvF : ∀ q m, GrF.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeF q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrF] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrF] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrF])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRF q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRF q) (Term.const 1) (hfRF q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRF hy

theorem edgeF_mem : ∀ st tgt, edgeF st tgt ∈ GrF.edges →
    edgeF st tgt ∈ GrF.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeF]⟩

theorem hfreshF : ∀ q m, GrF.modeAt q = some m →
    mvF ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvF q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The left window family (k = 5, plain windows) -/

noncomputable def leftDataF : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLF 0, domLF, 5), (fLF 1, domLF, 5)]

noncomputable def leftProgsF (dt : ℝ) : List (Program (Var 2)) :=
  leftDataF.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgF dt d.2.2)

theorem hLF : ∀ d ∈ leftDataF, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataF, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨hfLF 0 (by norm_num), hdomLF⟩
  · exact ⟨hfLF 1 (by norm_num), hdomLF⟩

theorem hframesF (dt : ℝ) : ∀ P ∈ leftProgsF dt, FramesMv P mvF := by
  intro P hP
  simp only [leftProgsF, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgF dt d.2.2 mvF (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## Parse pins -/

theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm2 : Run.parseRat "-2" = some (-2) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some 1 := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm005 : Run.parseRat "-0.05" = some (-(1:ℚ)/20) := by
  have h : parseQ "-0.05" = some (⟨-5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field pins (right constant rates, per mode) -/

theorem fRF0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRF q 0) x = (if q = 0 then (1:ℝ)/5 else 0 - 1/5) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, arm_fidelity_low_IR, vsF, Run.dynOf, Run.lowerE,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRF1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRF q 1) x = 0 := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, arm_fidelity_low_IR, vsF, Run.dynOf, Run.lowerE,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

/-! ## The dom/invariant shapes -/

theorem sat_domRF (x : State (Var 2)) : Formula.sat domRF x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) := by
  simp only [domRF, hostEvolve, mRF, arm_fidelity_low_IR, vsF]
  simp [Run.lowerF, Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem gF_eval (x : State (Var 2)) :
    Term.eval gF x = x (Lv 0) - (x (Rv 0) + 2/5) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gF, arm_fidelity_low_IR, Run.invToG, Run.lowerE, vsF, hp04,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

end ArmFidelityLowModal
end RelCertifier
