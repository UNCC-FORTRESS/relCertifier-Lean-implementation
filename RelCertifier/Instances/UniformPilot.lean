/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The uniform multi-flow grounding pilot: `rover_drag`

First benchmark instance of `theorem3_uniform_multiflow` (the paper-faithful window chain):
left = the clocked ε_L-window of the single `Cruise` mode; right = the transition-faithful
`Track` automaton; the within-window piece coupled by the JOINT flow certificate.

`rover_drag` is the honest pilot shape: ONE left mode, ONE right mode, so the only
(left-window, right-start) pair is the diagonal one, whose joint query is genuinely UNSAT
(`g = R_vx − L_vx − 0.05`, `ġ = 0.3(L_vx² − R_vx²) < 0` on `g = 0` within `vx ≥ 0`).
Multi-mode benchmarks (e.g. watertank) need the mode-correspondence loop invariant —
off-diagonal pairs have NO joint certificate (left `Low` vs right `High` is SAT) — which is
the reposition/region stage of task H, NOT this file.

All data is lowered from the parser-emitted IR (`Parse.rover_drag_IR`) — single source of
truth; nothing is hand-transcribed. State space is padded to `n = 2` (coordinate 1 inert)
to give the two fresh Aux slots `mv = (Aux, 0)`, `tg = (Aux, 1)`.

Residuals (named hypotheses, per the battery convention):
* `hz3` — the ONE joint flow query verdict (the `z3_unsat_sound` leaf);
* `hES` — the CSF duration-existence side condition (`HExistSeg`), as carried by
  `certified_relational`/`BridgeDischarge`; dischargeable later via the Picard bridge
  (the drag field pulls toward the interior equilibrium `vx = √(1/6) ≈ 0.408`);
* the encoding identity (`hψ`) and the invariant's projection splits.

The side-splits of the lowered fields/domains/invariant are NOT residuals: they are
kernel-proved via `LoweringSide` (lowering hygiene + a `rfl` prefix-freedom check on
the emitted IR).
-/
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Encoding.LoweringSide
import RelCertifier.Instances.BenchIR

namespace RelCertifier
namespace RoverDragPilot

open DL DLCalTiming DLRel Set Parse

/-! ## Lowered data (source of truth: the emitted IR) -/

/-- The state-variable table (`n = 2` pad: coordinate 1 has no ode, derivative 0). -/
def vsP : List String := ["vx"]

/-- Lowered left field of the single `Cruise` mode. -/
noncomputable def fLP : Fin 2 → Term (Var 2) := fun i =>
  (((rover_drag_IR.L.modes[0]?).bind (Run.dynOf vsP 2 Side.L)).map
    (fun f => (f i).toHost)).getD (Term.const 0)

/-- Lowered right field of the single `Track` mode. -/
noncomputable def fRP : Fin 2 → Term (Var 2) := fun i =>
  (((rover_drag_IR.R.modes[0]?).bind (Run.dynOf vsP 2 Side.R)).map
    (fun f => (f i).toHost)).getD (Term.const 0)

/-- Lowered left evolution domain. -/
noncomputable def domLP : Formula (Var 2) :=
  (((rover_drag_IR.L.modes[0]?).bind (fun m => Run.lowerF vsP 2 Side.L m.evolve)).map
    IForm.toHost).getD Formula.tt

/-- Lowered right evolution domain. -/
noncomputable def domRP : Formula (Var 2) :=
  (((rover_drag_IR.R.modes[0]?).bind (fun m => Run.lowerF vsP 2 Side.R m.evolve)).map
    IForm.toHost).getD Formula.tt

/-- The invariant's safe-side term: `g = (R_vx − L_vx) − 0.05`, invariant `g ≤ 0`. -/
noncomputable def gP : Term (Var 2) :=
  ((Run.invToG vsP 2 ((rover_drag_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-! ## The two graphs (right projection `Gr`, joint cover `Gj`) and the obligation -/

/-- The single right mode (`Track`, unstretched: λ = 1). -/
noncomputable def rModeP : RMode (Var 2) :=
  { sys := rightBlock fRP (Term.const 1), dom := domRP, weight := 1 }

/-- The declared self-loop `Track → Track` (guard ⊤, not pruned). -/
def selfEdgeP : REdge (Var 2) := { src := 0, tgt := 0, guard := Formula.tt, pruned := false }

/-- The right transition graph. -/
noncomputable def GrP : SearchGraph (Var 2) := { modes := [rModeP], edges := [selfEdgeP] }

/-- The joint cover mode (`Cruise ‖ Track` co-evolution). -/
noncomputable def jModeP : RMode (Var 2) :=
  { sys := jointSys fLP fRP (Term.const 1), dom := Formula.and domLP domRP, weight := 1 }

/-- The cover graph. -/
noncomputable def GjP : SearchGraph (Var 2) := { modes := [jModeP], edges := [selfEdgeP] }

/-- The one flow obligation: the joint Lie query of the diagonal pair at λ = 1. -/
noncomputable def obligP : FlowObligation 2 :=
  { g := gP, fL := fLP, fR := fRP, lam := Term.const 1,
    domain := Formula.and domLP domRP }

/-- Mode variable and window clock — the two Aux slots of the pad. -/
abbrev mvP : Var 2 := (Side.Aux, 0)
abbrev tgP : Var 2 := (Side.Aux, 1)

/-! ## Side-splits of the lowered data (kernel facts: `rfl` names-check + hygiene) -/

theorem hfLP : ∀ i, (fLP i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsP) _ (by simp [rover_drag_IR, Parse.PExpr.namesFree]) i x hx)

theorem hfRP : ∀ i, (fRP i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsP) _ (by simp [rover_drag_IR, Parse.PExpr.namesFree]) i x hx)

theorem hdomLP : domLP.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsP) _ (by simp [rover_drag_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem hdomRP : domRP.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsP) _ (by simp [rover_drag_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem hgLRP : gP.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

/-! ## Graph inversion and shape facts -/

theorem GrP_modeAt {q : ℕ} {m : RMode (Var 2)} (hm : GrP.modeAt q = some m) :
    q = 0 ∧ m = rModeP := by
  match q with
  | 0 =>
      refine ⟨rfl, ?_⟩
      simpa [SearchGraph.modeAt, GrP] using hm.symm
  | q + 1 => simp [SearchGraph.modeAt, GrP] at hm

theorem GrP_edge_mem {q : ℕ} {e : REdge (Var 2)} (he : e ∈ GrP.edgesFrom q) :
    e = selfEdgeP := by
  have hmem : e ∈ GrP.edges := List.mem_of_mem_filter he
  simpa [GrP] using hmem

theorem selfEdge_mem_from0 : selfEdgeP ∈ GrP.edgesFrom 0 :=
  List.mem_filter.mpr ⟨by simp [GrP], by simp [selfEdgeP]⟩

theorem httP : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  rw [GrP_edge_mem he]
  rfl

theorem hltP : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.tgt < GrP.modes.length := by
  intro q e he
  rw [GrP_edge_mem he]
  norm_num [GrP, selfEdgeP]

/-! ## The certificate bundle (Z3 leaf enters exactly once) -/

/-- The cover certificate of `GjP`: the one joint segment from `hz3` via
`segPres_from_flowCert`; every reposition/prune field vacuous (flags false, no pruned
edge); weights positive. -/
theorem coverCertP (hz3 : z3solve (flowQuery obligP) = Verdict.unsat) :
    CoverCert GjP gP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- segPres: the joint flow certificate
    intro q m hm hjOK
    have hq : q = 0 ∧ m = jModeP := by
      match q with
      | 0 =>
          refine ⟨rfl, ?_⟩
          simpa [SearchGraph.modeAt, GjP] using hm.symm
      | q + 1 => simp [SearchGraph.modeAt, GjP] at hm
    rw [hq.2]
    exact segPres_from_flowCert obligP hz3
  · -- repoPresPre: no mode carries it
    intro q m hm hflag
    have : m = jModeP := by
      match q with
      | 0 => simpa [SearchGraph.modeAt, GjP] using hm.symm
      | q + 1 => simp [SearchGraph.modeAt, GjP] at hm
    subst this
    simp [jModeP] at hflag
  · intro q m hm hflag
    have : m = jModeP := by
      match q with
      | 0 => simpa [SearchGraph.modeAt, GjP] using hm.symm
      | q + 1 => simp [SearchGraph.modeAt, GjP] at hm
    subst this
    simp [jModeP] at hflag
  · intro q m hm hflag
    have : m = jModeP := by
      match q with
      | 0 => simpa [SearchGraph.modeAt, GjP] using hm.symm
      | q + 1 => simp [SearchGraph.modeAt, GjP] at hm
    subst this
    simp [jModeP] at hflag
  · intro q m hm hflag
    have : m = jModeP := by
      match q with
      | 0 => simpa [SearchGraph.modeAt, GjP] using hm.symm
      | q + 1 => simp [SearchGraph.modeAt, GjP] at hm
    subst this
    simp [jModeP] at hflag
  · -- pruneSound: no pruned edge
    intro e he hpr
    have : e = selfEdgeP := by simpa [GjP] using he
    subst this
    simp [selfEdgeP] at hpr
  · -- weightPos
    intro m hm
    have : m = jModeP := by simpa [GjP] using hm
    subst this
    norm_num [jModeP]

/-! ## The projection alignment and the emitted window -/

theorem rpaP (hfL : ∀ i, (fLP i).fv ⊆ range Lv) (hfR : ∀ i, (fRP i).fv ⊆ range Rv)
    (hdomR : domRP.fv ⊆ range Rv)
    (hES : ∀ ν, HExistSeg fLP fRP (Term.const 1) domLP domRP ν) :
    RightProjAlignV GjP GrP gP fLP domLP := by
  intro q m' hm'
  obtain ⟨rfl, rfl⟩ := GrP_modeAt hm'
  refine ⟨fRP, Term.const 1, domRP, jModeP, rfl, rfl,
    LR_blocks_disjoint fLP fRP (Term.const 1) hfL hfR (by simp [Term.fv]),
    ?_, rfl, rfl, rfl, rfl, hES⟩
  intro x hx
  obtain ⟨i, rfl⟩ := hdomR hx
  exact Or.inl (Rv_mem_rightBlock_boundSet fRP (Term.const 1) i)

/-- The emitted window response: `k = 1` — the single self-mode piece. -/
theorem emitP (hfL : ∀ i, (fLP i).fv ⊆ range Lv) (hdomL : domLP.fv ⊆ range Lv)
    (hfR : ∀ i, (fRP i).fv ⊆ range Rv) (hdomR : domRP.fv ⊆ range Rv) :
    EmitWindows GrP gP mvP fLP domLP tgP 1 1 := by
  intro q hq σ hmv hσ
  have hq0 : q = 0 := by
    have : GrP.modes.length = 1 := rfl
    omega
  subst hq0
  refine ⟨[(0, rModeP, selfEdgeP)], rfl, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨rfl, selfEdge_mem_from0⟩
  · simp
  · intro s hs
    simp only [List.head?_cons, Option.some.injEq] at hs
    rw [← hs]
  · intro Q hQ
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hQ
    subst hQ
    rw [Set.disjoint_left]
    intro x hxR hxL
    have hR : x ∈ ({mvP, mvP} : Set (Var 2)) ∪ range Rv := by
      rw [Program.rename_refl] at hxR
      have hsub : (rModeP.sys.boundSet ∪ rModeP.sys.readVars ∪ rModeP.dom.fv)
          ⊆ range Rv := by
        intro y hy
        rcases hy with (hy | hy) | hy
        · exact rightBlock_boundSet_sub fRP (Term.const 1) hy
        · exact rightBlock_readVars_sub fRP (Term.const 1) hfR (by simp [Term.fv]) hy
        · exact hdomR hy
      exact Or.inr (hsub (vars_ode_sub rModeP.sys rModeP.dom hxR))
    have hL : x ∈ ({tgP} : Set (Var 2)) ∪ range Lv :=
      vars_clockedSegL_sub fLP domLP 1 1 hfL hdomL hxL
    exact absurd hxR (by
      rcases hL with hx | ⟨i, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rcases hR with hx | hx
        · simp [mvP, tgP, Prod.ext_iff] at hx
        · exact absurd hx (aux_notin_range_Rv 1)
      · rcases hR with hx | ⟨j, hj⟩
        · exact absurd hx.symm (by intro h; exact absurd h (by
            simp [mvP, Lv, Prod.ext_iff]))
        · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
      )

/-! ## The pilot theorem -/

/-- **`rover_drag`, multi-flow window chain, end to end.** The left `Cruise` window
(one clock-capped piece, `dt = ε_R/λ = 1`) against the transition-faithful `Track`
automaton; the piece coupled by the joint flow certificate `hz3` — the single Z3 leaf.
Residuals: the encoding identity and invariant splits, `hz3`, `hES` — the side-splits
of the lowered data are kernel facts (`LoweringSide` + `rfl` names-check on the IR). -/
theorem rover_drag_multiflow
    (ϕinv : RFormula (Var 2))
    (hψ : encode (Equiv.refl (Var 2)) ϕinv = invLe gP)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hz3 : z3solve (flowQuery obligP) = Verdict.unsat)
    (hES : ∀ ν, HExistSeg fLP fRP (Term.const 1) domLP domRP ν) :
    RFormula.rvalid (theorem3Form
      (bigChoice ([(fLP, domLP, 1)].map (fun d =>
        windowSeg (leftBlock d.1) d.2.1 tgP 1 d.2.2)))
      (rightAutomatonBody GrP mvP)
      (RFormula.and ϕinv (mvValidR mvP GrP.modes.length))) := by
  refine uniform_multiflow_end_to_end GrP gP 0 1 1 [(fLP, domLP, 1)] ϕinv
    (by decide) hψ hgLRP httP hltP ?_ ?_ hinvL hinvR ?_
  · -- the right modes live on Rv
    intro q m hm
    obtain ⟨rfl, rfl⟩ := GrP_modeAt hm
    intro y hy
    rcases hy with (hy | hy) | hy
    · exact rightBlock_boundSet_sub fRP (Term.const 1) hy
    · exact rightBlock_readVars_sub fRP (Term.const 1) hfRP (by simp [Term.fv]) hy
    · exact hdomRP hy
  · -- the left window lives on Lv
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact ⟨hfLP, hdomLP⟩
  · -- the load-bearing cover data
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact ⟨⟨GjP, coverCertP hz3, rpaP hfLP hfRP hdomRP hES⟩, emitP hfLP hdomLP hfRP hdomRP⟩

end RoverDragPilot
end RelCertifier
