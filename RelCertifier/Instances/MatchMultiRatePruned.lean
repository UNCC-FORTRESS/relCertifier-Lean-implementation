/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` with its pruned `STALL` fallback — Theorem 3 over the enlarged
automaton, and the non-connection certificate (Theorem 2) of the pruned edge

`benchmarks/suite_uniform/match_multi_rate/input.txt` declares (2026-10-08, additively)
a stall fallback on the right: `STALL` (`v' = −2v`, `s' = v`, guard `v < 0.2`, self-loop
only) with the single declared edge `DRIVE → STALL`. The certifier PRUNES that edge by a
non-connection certificate (paper Section 4.3): no `DRIVE` entry state has `v < 0.2`
(`DRIVE`'s guard is `0.2 ≤ v ≤ 1`), and on the threshold `v = 0.2` the `DRIVE` field is
`v' = 1 − v = 0.8 > 0`, so the right flow moves strictly away from it. Without pruning
(`RELCERT_NO_PRUNE=1`) the `FAST` and `MEDIUM` windows, whose covers take 3 and 2 `DRIVE`
segments, owe the uncertifiable `STALL` successor and the benchmark is DECLINED; with
pruning it is CERTIFIED as before (`docs/PRUNING.md`, with both runs).

**Theorem 3 over the enlarged automaton** (`match_multi_rate_pruned`). The base instance
`MatchMultiRateModal.match_multi_rate_modal` states Theorem 3 over the one-mode right
automaton `GrM` (`DRIVE` only). The file's automaton now has two modes; the statement
below ranges over it — `GrP = GrM` with `STALL` appended and the edges `DRIVE → STALL`,
`STALL → STALL` — with the mode-REGION bookkeeping `mvRegionR` at `regionsP`: `⊤` at
`DRIVE`, `⊥` at `STALL` (`Proofs/Encoding/SinkExtension.lean`). It reads: from every
state satisfying the declared invariant `v_L ≤ v_R` with the right in `DRIVE`, the
refinement is maintained and the right never enters `STALL`. The plain `mvValid`
statement over the two-mode automaton is FALSE — from `mv = STALL` the right can only
decay or stand still while a left window accelerates, so no response exists — and the
region form is exactly what the non-connection certificate licenses: the only edge into
`STALL` is never taken. The witness is the base instance's (`HmultiM`: in-place `DRIVE`
pieces at the per-window stretch), lifted edge by edge; the pruned edge is never in it.
The verdict hypotheses are the base instance's four `VerdM` packs, unchanged (same runner
row, same pins).

**The pruned edge's certificate** (`match_multi_rate_nonconn`). The two queries the
certifier sent Z3 to prune `DRIVE → STALL` — `Trusted/NonConnQuery.lean`, rebuilt and
re-run by `relcert --run-verdicts` phase 5 (`Verdicts/RunNonConn.lean`), pinned to this
file's hypothesis by `Verdicts/NonConnPins.lean` — are stated here as `VerdNC`, and
`Proofs/Encoding/NonConnBridge.lean` turns them into Theorem 2's conclusion: from every
`DRIVE` entry state (guard ∧ evolve ∧ `DRIVE`'s checked cut), along `DRIVE`'s right flow
with the left frozen, `v_R < 0.2` never holds. Axioms: the standard three plus
`z3_unsat_sound` at the two verdicts. Theorem 3 above does not consume it.
-/
import RelCertifier.Instances.MatchMultiRateModal
import RelCertifier.Instances.EvolStrengthenings.match_multi_rate
import RelCertifier.Proofs.Encoding.SinkExtension
import RelCertifier.Proofs.Encoding.CutComposition
import RelCertifier.Proofs.Encoding.NonConnBridge

namespace RelCertifier
namespace MatchMultiRatePruned

open DL DLCalTiming DLRel Parse Set MatchMultiRateModal

set_option maxHeartbeats 1600000

/-! ## The enlarged right automaton: `DRIVE` (0), `STALL` (1) -/

/-- `GrM` with `STALL` (`mRM 1`, at the uniform right evolve) and the two declared edges
`DRIVE → STALL`, `STALL → STALL` appended. -/
noncomputable def GrP : SearchGraph (Var 2) := GrM.extend (modeM 1) [edgeM 0 1, edgeM 1 1]

theorem GrP_modes_length : GrP.modes.length = 2 := rfl

/-- `STALL`'s field reads only right variables (the same pipeline fact as `hfRM`, now
for both right modes). -/
theorem hfRM' (q : ℕ) (hq : q < 2) : ∀ i, (fRM q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsM) (some (mRM q))
    (by interval_cases q <;>
      simp [mRM, match_multi_rate_IR, Parse.PExpr.namesFree]) i x
    (fRM_pipe q i ▸ hx))

theorem hRvP : ∀ q m, GrP.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv :=
  extend_hRv GrM (modeM 1) _ hRvM (by
    intro y hy
    rcases hy with (hy | hy) | hy
    · exact rightBlock_boundSet_sub (fRM 1) (Term.const 1) hy
    · exact rightBlock_readVars_sub (fRM 1) (Term.const 1) (hfRM' 1 (by norm_num))
        (by simp [Term.fv]) hy
    · exact hdomRM hy)

theorem httP : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.guard = Formula.tt :=
  extend_htt GrM (modeM 1) _ httM (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl)

theorem hltP : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.tgt < GrP.modes.length :=
  extend_hlt GrM (modeM 1) _ hltM (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [GrM, edgeM])

theorem hfreshP : ∀ q m, GrP.modeAt q = some m → mvM ∉ (Program.ode m.sys m.dom).fv :=
  extend_hfresh GrM (modeM 1) _ 0 hRvP

/-- The mode regions: `⊤` at `DRIVE`, `⊥` at `STALL`. -/
noncomputable def regionsP : ℕ → Formula (Var 2) := sinkRegions GrM.modes.length

/-! ## Theorem 3 over the enlarged automaton -/

/-- **`match_multi_rate`, modal Theorem 3 over the two-mode right automaton**, at the
declared invariant `v_L ≤ v_R`, with the right never in `STALL` (`mvRegionR` at
`regionsP`). The response is the base instance's; the pruned edge is never taken.
Hypotheses: the base instance's four `VerdM` packs. -/
theorem match_multi_rate_pruned (dt : ℝ) (hdt : 0 ≤ dt)
    (hv0 : VerdM 0) (hv1 : VerdM 1) (hv2 : VerdM 2) (hv3 : VerdM 3) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsM dt))
      (rightAutomatonBody GrP mvM)
      (RFormula.and (RFormula.and (canonInvM gM gsM) (envLR domLM domRM))
        (mvRegionR mvM regionsP GrP.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrP mvM (FM gM gsM) domLM domRM regionsP
    (leftProgsM dt) (canonInvM gM gsM) (encode_canonInvM gM gsM) ?_ ?_ ?_
  · exact hdis_multi GrP 0 1 dt leftDataM (by decide) httP hRvP hLM
  · exact hstep_assembled_multiR GrP mvM (FM gM gsM) envM regionsP (leftProgsM dt)
      hmvFM hmvenvM (fun q => notMem_sinkRegions_fv _ q mvM) hfreshP httP hltP
      (hframesM dt)
      (Hmulti_sink_extend GrM mvM (FM gM gsM) envM (leftProgsM dt) (modeM 1)
        [edgeM 0 1, edgeM 1 1] hltM (HmultiM dt hdt hv0 hv1 hv2 hv3))
  · exact hddF_multiR_plain GrP 0 1 dt leftDataM regionsP (canonInvM gM gsM) domLM domRM
      (by decide) httP hRvP hLM (fun q _ => sinkRegions_fv_sub _ q)
      (canonInvM_varsL gM gsM (by
        intro g' hg'
        simp only [gM, gsM, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gM gsM) hdomLM hdomRM

/-! ## The pruned edge `DRIVE → STALL`: the certifier's two queries, pinned -/

open NonConn

theorem hm02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- `STALL`'s guard `v < 0.2` as the safe-side term `g = 0.2 − v` (`{g > 0}` is the guard). -/
def gD : ITerm 2 := .bin .sub (.rat ((1:ℚ)/5)) (.var (Side.R, 0))

/-- `DRIVE`'s evolve `s ≥ 0 ∧ v ≥ 0 ∧ v ≤ 1.15`, lowered on the right. -/
def domD : IForm 2 :=
  .and (.and (.cmp .ge (.var (Side.R, 1)) (.rat 0)) (.cmp .ge (.var (Side.R, 0)) (.rat 0)))
    (.cmp .le (.var (Side.R, 0)) (.rat ((23:ℚ)/20)))

/-- `DRIVE`'s guard `0.2 ≤ v ≤ 1` conjoined with its evolve (the entry region). -/
def srcD : IForm 2 :=
  .and (.and (.cmp .ge (.var (Side.R, 0)) (.rat ((1:ℚ)/5)))
    (.cmp .le (.var (Side.R, 0)) (.rat 1))) domD

/-- `DRIVE`'s checked cut: its two guard atoms (`shape`-route, emitted certificate),
folded as `checkedCut` folds them. -/
def cutD : IForm 2 :=
  .and (.and .tt (.cmp .ge (.var (Side.R, 0)) (.rat ((1:ℚ)/5))))
    (.cmp .le (.var (Side.R, 0)) (.rat 1))

/-- `DRIVE`'s lowered field: `v' = 1·(1 − v)`, `s' = v`. -/
def fD : Fin 2 → ITerm 2 := fun i =>
  (([ITerm.bin .mul (.rat 1) (.bin .sub (.rat 1) (.var (Side.R, 0))),
    ITerm.var (Side.R, 0)] : List (ITerm 2))[i.val]?).getD (.rat 0)

theorem hgD : guardTerm vsM 2 (mRM 1).guard = some gD := by
  simp [guardTerm, mRM, match_multi_rate_IR, vsM, Run.lowerE, Run.resolveVar, hm02,
    List.findIdx?_cons, gD]

theorem hdomD : Run.lowerF vsM 2 Side.R (mRM 0).evolve = some domD := by
  simp [Run.lowerF, mRM, match_multi_rate_IR, vsM, Run.lowerE, Run.resolveVar, hm00,
    hm115, List.findIdx?_cons, domD]

theorem hsrcD : Run.lowerF vsM 2 Side.R (PForm.and (mRM 0).guard (mRM 0).evolve)
    = some srcD := by
  simp [Run.lowerF, mRM, match_multi_rate_IR, vsM, Run.lowerE, Run.resolveVar, hm00,
    hm115, hm02, hm10, List.findIdx?_cons, srcD, domD]

theorem hdynD : Run.dynOf vsM 2 Side.R (mRM 0) = some fD := by
  simp [Run.dynOf, mRM, match_multi_rate_IR, vsM, Run.lowerE, Run.resolveVar, hm1, hm10,
    List.findIdx?_cons, List.finRange]
  rfl

theorem hcutD : cutOfAtoms vsM 2 (rightCutAtoms Oracle.match_multi_rate_cuts "DRIVE")
    = some cutD := by
  simp [cutOfAtoms, rightCutAtoms, Oracle.match_multi_rate_cuts, vsM, Run.lowerF,
    Run.lowerE, Run.resolveVar, hm02, hm10, List.findIdx?_cons, cutD]

/-- The certifier's two pruning queries for `DRIVE → STALL` are exactly the pair below
(`Trusted/NonConnQuery.lean`, the function `nonConnPrune` calls). -/
theorem queriesD :
    queries vsM 2 cutD (mRM 0) (mRM 1) = some (srcQuery gD srcD cutD, barQuery gD domD cutD fD) :=
  queries_eq hgD hdomD hsrcD hdynD

/-- The two verdicts the certifier observed to prune `DRIVE → STALL`: the source check
and the barrier check, both `unsat`. Re-run by `relcert --run-verdicts` (phase 5). -/
def VerdNC : Prop :=
  z3solve (srcQuery gD srcD cutD).toHost = Verdict.unsat ∧
  z3solve (barQuery gD domD cutD fD).toHost = Verdict.unsat

/-- The lowered `DRIVE` field is the base instance's `fRM 0`. -/
theorem fD_eq_fRM : (fun i => (fD i).toHost) = fRM 0 := by
  funext i
  simp [fRM, hostDyn, hdynD]

/-- **Theorem 2 for the pruned edge.** From every `DRIVE` entry state (guard ∧ evolve ∧
cut), every state the `DRIVE` right flow reaches — the left frozen, inside the
cut-narrowed evolve domain — has `v_R ≥ 0.2`: the `STALL` guard never fires along it. -/
theorem match_multi_rate_nonconn (h : VerdNC) :
    ∀ ν, Formula.sat (IForm.and srcD cutD).toHost ν →
      ∀ ω, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRM 0) (Term.const 1))
          (IForm.and domD cutD).toHost) ν ω →
        ¬ Formula.sat (Formula.cmp .gt gD.toHost (Term.const 0)) ω := by
  rw [← fD_eq_fRM]
  exact nonconn_of_unsat gD domD srcD cutD fD h.1 h.2

/-- The conclusion, read off: `0.2 ≤ v_R` at every reached state. -/
theorem match_multi_rate_nonconn' (h : VerdNC) :
    ∀ ν, Formula.sat (IForm.and srcD cutD).toHost ν →
      ∀ ω, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRM 0) (Term.const 1))
          (IForm.and domD cutD).toHost) ν ω →
        (1:ℝ)/5 ≤ ω (Rv 0) := by
  intro ν hν ω hω
  have := match_multi_rate_nonconn h ν hν ω hω
  simp only [gD, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp] at this
  push_cast at this
  linarith [not_lt.mp (fun hlt => this hlt)]

end MatchMultiRatePruned
end RelCertifier
