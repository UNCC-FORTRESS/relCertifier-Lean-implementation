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

STATUS (2026-07-30). Kept as the **only** instantiation of `theorem3_uniform_multiflow`
anywhere in the tree — that is its remaining value. It is no longer the `rover_drag`
deliverable: `Instances/RoverDragModal.lean` (`rover_drag_modal`) carries that benchmark's
Theorem 3 through the modal chain, and is audited in `Instances/ModalBattery.lean`. The
open items this header once listed are closed: the mode-correspondence loop invariant is
`WatertankModal`/`EnvelopeChainR`, and `hES` is discharged by
`Proofs/Flow/ViabilityWiring.lean` (and, per benchmark, in the modal instances).
-/
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Encoding.LoweringSide
import RelCertifier.Proofs.Encoding.CoverExtract
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Instances.BenchIR.rover_drag

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

/-- Self-edges declared (the `next` list contains the mode itself — input condition). -/
theorem hselfP : ∀ q, q < GrP.modes.length → ∃ e ∈ GrP.edgesFrom q, e.tgt = q := by
  intro q hq
  have hq0 : q = 0 := by
    have : GrP.modes.length = 1 := rfl
    omega
  subst hq0
  exact ⟨selfEdgeP, selfEdge_mem_from0, rfl⟩

/-- Per-mode footprint disjointness against the clocked left (side-splits). -/
theorem hdisP : ∀ q m, GrP.modeAt q = some m →
    Disjoint (Program.vars ((Program.ode m.sys m.dom).rename (Equiv.refl (Var 2))))
      (Program.vars (clockedSeg (leftBlock fLP) domLP tgP 1)) := by
  intro q m hm
  obtain ⟨rfl, rfl⟩ := GrP_modeAt hm
  rw [Set.disjoint_left]
  intro x hxR hxL
  have hR : x ∈ range Rv := by
    rw [Program.rename_refl] at hxR
    have hsub : (rModeP.sys.boundSet ∪ rModeP.sys.readVars ∪ rModeP.dom.fv)
        ⊆ range Rv := by
      intro y hy
      rcases hy with (hy | hy) | hy
      · exact rightBlock_boundSet_sub fRP (Term.const 1) hy
      · exact rightBlock_readVars_sub fRP (Term.const 1) hfRP (by simp [Term.fv]) hy
      · exact hdomRP hy
    exact hsub (vars_ode_sub rModeP.sys rModeP.dom hxR)
  have hL : x ∈ ({tgP} : Set (Var 2)) ∪ range Lv :=
    vars_clockedSegL_sub fLP domLP 1 1 hfLP hdomLP hxL
  rcases hL with hx | ⟨i, rfl⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact aux_notin_range_Rv 1 hR
  · obtain ⟨j, hj⟩ := hR
    exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The tool's cover decision, re-run by the kernel** (`k = bBudget = 1`, σ = preJ):
the very `decideCovered` the tool gates CERTIFIED on, replayed as a kernel fact. -/
theorem rover_drag_covered :
    decideCovered GjP 2 ⟨0, 1, SrcSetting.preJ⟩ = true := by decide

/-! ## The pilot theorem -/

/-- **`rover_drag`, multi-flow window chain, end to end.** The left `Cruise` window
(one clock-capped piece, `dt = ε_R/λ = 1`) against the transition-faithful `Track`
automaton; the piece coupled by the joint flow certificate `hz3` — the single Z3 leaf.
Residuals: `hz3` (one joint verdict), `hES` (duration existence) — nothing else. The
relational invariant is the canonical `canonInv gP` (R3), its encoding identity and
projection splits proved generically; the lowered-data side-splits are kernel facts. -/
theorem rover_drag_multiflow
    (hz3 : z3solve (flowQuery obligP) = Verdict.unsat)
    (hES : ∀ ν, HExistSeg fLP fRP (Term.const 1) domLP domRP ν) :
    RFormula.rvalid (theorem3Form
      (bigChoice ([(fLP, domLP, 1)].map (fun d =>
        windowSeg (leftBlock d.1) d.2.1 tgP 1 d.2.2)))
      (rightAutomatonBody GrP mvP)
      (RFormula.and (canonInv gP) (mvValidR mvP GrP.modes.length))) := by
  refine uniform_multiflow_end_to_end GrP gP 0 1 1 [(fLP, domLP, 1)] (canonInv gP)
    (by decide) (encode_canonInv gP) hgLRP httP hltP ?_ ?_
    (canonInv_varsL gP hgLRP) (canonInv_varsR gP) ?_
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
    exact ⟨⟨GjP, coverCertP hz3, rpaP hfLP hfRP hdomRP hES⟩,
      emitWindows_self GrP gP mvP tgP fLP domLP 1 1 hselfP hdisP⟩

end RoverDragPilot
end RelCertifier
