/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The bridge verdict runner (Appendix B.4, pinning the queries)

Per benchmark, at the bridge dimension (`bridgeDimV2`: the Assumption 1 lemma's dimension,
the state variables plus the auxiliary coordinates the instance needs, plus one for the right
clock), every group of `Emitted.bridgeGroups` is sent to
Z3; a group is discharged when one member is `unsat` (a flow pack's component by any of its
three routes, every other group by its single query). The groups are exactly the queries
`Emitted.verdicts_of_groups` reads as the `Verdicts` structure the generic instances assume.
-/
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.StrictRun
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.Trusted.Sos
import RelCertifier.InstancesV2.BenchProgress
import RelCertifier.InstancesV2.BenchChoice
import RelCertifier.InstancesV2.BenchPrelanding
import RelCertifier.InstancesV2.Choice.BenchIR.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.BenchIR.watertank_choice
import RelCertifier.InstancesV2.Choice.Cuts.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.Cuts.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchCovers.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.BenchCovers.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchProgress.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.BenchProgress.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchChoice.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.BenchChoice.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchPrelanding.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.BenchPrelanding.watertank_choice

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Oracle RelCertifier.Emitted RelCertifier.Progress RelCertifier.Choice

/-- A benchmark's records at its bridge dimension. -/
structure BridgeRec where
  name : String
  dim  : ℕ
  ir   : PProblem
  cuts : EvolStrengtheningX
  cov  : CoverEmitE
  prog : ProgressEmitE
  ce   : ChoiceEmitE

/-- The two exhibits of committed successor subsets (`benchmarks/choice`): their records, at the
hand-written general instance's dimension plus the right clock (`bridgeDimV2`'s rule), each cover
merged with its pre-landing record (`withPL`, the instance's `covM`): both check right-only flow
certificates on the restricted mode (Lemma 4). -/
def choiceRecsV2 : List BridgeRec :=
  [ ⟨"vehicle_accel_copy", 2 + 1, vehicle_accel_copy_IRc, vehicle_accel_copy_cutsCX,
      withPL vehicle_accel_copy_coverV2 Preland.vehicle_accel_copy_coverV2_prelanding,
      vehicle_accel_copy_coverV2_progress, vehicle_accel_copy_coverV2_choice⟩,
    ⟨"watertank_choice", 2 + 1, watertank_choice_IRc, watertank_choice_cutsCX,
      withPL watertank_choice_coverV2 Preland.watertank_choice_coverV2_prelanding,
      watertank_choice_coverV2_progress, watertank_choice_coverV2_choice⟩ ]

-- `coverV2`, `coverV2M` (the cover merged with the pre-landing record) and `progV2` are in
-- `VerdictsV2/RunV2.lean` (its right-only phase reads the same records).

def choiceV2 (b : String) : ChoiceEmitE :=
  ((choiceTableV2.find? (·.1 == b)).map (·.2)).getD (ChoiceEmitE.empty b)

/-- The dimensions of the benchmarks whose Assumption 1 lemma comes from a hand-written general
exhibit (`InstancesV2/Choice/General/`): the dimension at which the exhibit proves Assumption 1.
Empty: every suite benchmark has its own `InstancesV2/WellFormed/` proof. -/
def generalDimsV2 : List (String × ℕ) := []

/-- The bridge dimension of a benchmark: the dimension of its Assumption 1 lemma (the pack
table's; else a hand-written general instance's, `generalDimsV2`; else the state variables
padded to three coordinates, the right mode variable, the left clock and the stored left mode)
PLUS ONE, the right clock `(Aux, d)` of the clocked right automaton (`rightAutomatonBodyC`):
the fourth auxiliary coordinate of the keyed form, the third of the window form. Assumption 1
is lifted from the lemma's dimension by `Emitted.wellFormedR_lift`. -/
def bridgeDimV2 (b : String) : ℕ :=
  ((packsV2.find? (fun r => r.bench == b)).map (fun r => r.dim)).getD
    (((generalDimsV2.find? (·.1 == b)).map (·.2)).getD (max (irV2 b).L.stateVars.length 3)) + 1

/-- Declared: the number of query groups over the bridge instances, the 50 suite benchmarks and
the two exhibits of committed successor subsets (13677 groups over 52 instances, Appendix B.4).
Every right-only node is checked on its restricted mode (the cover merged with its pre-landing
record, its pack on its region, routes A/B/C per component). -/
def expectedBridgeGroupsV2 : Nat := 13677

/-- The suite's records. -/
def suiteRecV2 (b : String) : BridgeRec :=
  ⟨b, bridgeDimV2 b, irV2 b, cutV2 b, coverV2M b, progV2 b, choiceV2 b⟩

/-- Discharge a list of groups: a group is discharged when a member is `unsat`. With `sos`
set the SOS oracle is tried on a member Z3 answers `unknown` on (`Trusted/Sos.lean`; the
flow groups only, `bridgeGroupsFlowS`, the hypothesis `GroupsOKT` of `verdictsS_of_tagged`);
returns (all discharged, groups, groups discharged by the SOS oracle). -/
def runGroups (s : Z3Session) (sos : Option Nat) (b : String) {n : ℕ} (coord : Fin n → String)
    (gs : List (List (IForm n))) : IO (Bool × Nat × Nat) := do
  let mut bad := 0
  let mut bySos := 0
  let mut gi := 0
  for g in gs do
    let mut hit := false
    let mut mi := 0
    for q in g do
      if !hit then
        match ← oracleCheck s sos (q.toScript coord) s!"[sos secs={sos.getD 0}] {b} group#{gi} member#{mi}" with
        | .ok (.unsat, t) =>
            hit := true
            if t == .sos then bySos := bySos + 1
        | _ => pure ()
      mi := mi + 1
    if hit then RelCertifier.Verdicts.counted
    else bad := bad + 1
    gi := gi + 1
  pure (bad == 0, gs.length, bySos)

def runBridgeBench (s : Z3Session) (k : Option ℕ) (r : BridgeRec) : IO (Bool × Nat) := do
  let b := r.name
  let p := r.ir
  let n := r.dim
  let vars := p.L.stateVars
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  let sos ← sosSecsFromEnv
  -- the strict groups (`bridgeGroupsS`, read as `VerdictsS`); the existing groups exactly
  -- when no row has a strict atom (`bridgeGroupsS_eq_of_noStrict`). With `RELCERT_SOS_SECS`
  -- set the three parts are sent in the same order, the SOS oracle on the flow part only
  -- (`verdictsS_of_tagged`)
  match sos with
  | none =>
      match bridgeGroupsS p n r.cuts r.cov r.prog r.ce k with
      | none =>
          IO.println s!"  FAIL  {b}  (the query groups did not rebuild)"
          pure (false, 0)
      | some gs =>
          let (ok, cnt, _) ← runGroups s none b coord gs
          if ok then IO.println s!"  UNSAT {b}  ({cnt} groups, dim {n})"
          else IO.println s!"  FAIL  {b}  (some of {cnt} groups not discharged, dim {n})"
          pure (ok, cnt)
  | some _ =>
      match bridgeGroupsPre p n r.cuts r.cov, bridgeGroupsFlowS p n r.cuts r.cov r.prog k,
          bridgeGroupsPostS p n r.cuts r.cov r.prog r.ce with
      | some gP, some gF, some gQ =>
          let (okP, cP, _) ← runGroups s none b coord gP
          let (okF, cF, bySos) ← runGroups s sos b coord gF
          let (okQ, cQ, _) ← runGroups s none b coord gQ
          let ok := okP && okF && okQ
          let cnt := cP + cF + cQ
          if ok then IO.println s!"  UNSAT {b}  ({cnt} groups, dim {n}, {bySos} by the SOS oracle)"
          else IO.println s!"  FAIL  {b}  (some of {cnt} groups not discharged, dim {n}, {bySos} by the SOS oracle)"
          pure (ok, cnt)
      | _, _, _ =>
          IO.println s!"  FAIL  {b}  (the query groups did not rebuild)"
          pure (false, 0)

def runBridgeV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 bridge verdicts : {benchIRTableV2.length} benchmarks =="
      -- the hypothesis-slicing knob (`docs/HYP-SLICING.md`): the flow groups are sliced with the
      -- tool's own function, the instances' `Verdicts` are their sliced verdicts (`Z3Unsat`)
      let hops ← sliceHopsFromEnv
      if let some h := hops then IO.println s!"  [slice] RELCERT_SLICE_HOPS={h}: the flow groups are sliced"
      if let some secs ← sosSecsFromEnv then
        IO.println s!"  [sos] RELCERT_SOS_SECS={secs}: the SOS oracle on the flow groups Z3 leaves unknown"
      let mut ok := true
      let mut total := 0
      for rec in benchIRTableV2.map (fun x => suiteRecV2 x.1) ++ choiceRecsV2 do
        let (r, k) ← runBridgeBench s hops rec
        ok := r && ok
        total := total + k
      s.close
      let k ← RelCertifier.Verdicts.dischargedCount.get
      IO.println s!"  [bridge] {total} groups over the suite"
      let full ← RelCertifier.Verdicts.checkPhase "bridge" k expectedBridgeGroupsV2
      pure (ok && full)

end RelCertifier.VerdictsV2
