/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The bridge verdict runner

Per benchmark, at the bridge dimension (the pack table's `dim`: the state variables plus the
auxiliary coordinates the instance needs), every group of `Emitted.bridgeGroups` is sent to
Z3; a group is discharged when one member is `unsat` (a flow pack's component by any of its
three routes, every other group by its single query). The groups are exactly the queries
`Emitted.verdicts_of_groups` reads as the `Verdicts` structure the generic instances assume.
-/
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.InstancesV2.BenchProgress
import RelCertifier.InstancesV2.BenchChoice
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

/-- The choice exhibits (`benchmarks/choice`): their records. -/
def choiceRecsV2 : List BridgeRec :=
  [ ⟨"vehicle_accel_copy", 2, vehicle_accel_copy_IRc, vehicle_accel_copy_cutsCX, vehicle_accel_copy_coverV2,
      vehicle_accel_copy_coverV2_progress, vehicle_accel_copy_coverV2_choice⟩,
    ⟨"watertank_choice", 2, watertank_choice_IRc, watertank_choice_cutsCX, watertank_choice_coverV2,
      watertank_choice_coverV2_progress, watertank_choice_coverV2_choice⟩ ]

def coverV2 (b : String) : CoverEmitE :=
  ((coverTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, [], []⟩

def progV2 (b : String) : ProgressEmitE :=
  ((progressTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, []⟩

def choiceV2 (b : String) : ChoiceEmitE :=
  ((choiceTableV2.find? (·.1 == b)).map (·.2)).getD (ChoiceEmitE.empty b)

/-- The dimensions of the benchmarks whose Assumption 1 lemma comes from a hand-written general
instance (`InstancesV2/Choice/General/`), the instance's own dimension. -/
def generalDimsV2 : List (String × ℕ) := [("vehicle_hypercert", 2)]

/-- The bridge dimension of a benchmark: the pack table's; else a hand-written general instance's
(`generalDimsV2`); else the state variables padded to the three auxiliary coordinates the keyed
form needs. -/
def bridgeDimV2 (b : String) : ℕ :=
  ((packsV2.find? (fun r => r.bench == b)).map (fun r => r.dim)).getD
    (((generalDimsV2.find? (·.1 == b)).map (·.2)).getD (max (irV2 b).L.stateVars.length 3))

/-- Declared: the number of query groups over the suite. -/
def expectedBridgeGroupsV2 : Nat := 4457

/-- The suite's records. -/
def suiteRecV2 (b : String) : BridgeRec :=
  ⟨b, bridgeDimV2 b, irV2 b, cutV2 b, coverV2 b, progV2 b, choiceV2 b⟩

def runBridgeBench (s : Z3Session) (r : BridgeRec) : IO (Bool × Nat) := do
  let b := r.name
  let p := r.ir
  let n := r.dim
  let vars := p.L.stateVars
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  match bridgeGroups p n r.cuts r.cov r.prog r.ce with
  | none =>
      IO.println s!"  FAIL  {b}  (the query groups did not rebuild)"
      pure (false, 0)
  | some gs =>
      let mut ok := true
      let mut bad := 0
      for g in gs do
        let mut hit := false
        for q in g do
          if !hit then
            match ← s.check (q.toScript coord) with
            | .ok .unsat => hit := true
            | _ => pure ()
        if hit then RelCertifier.Verdicts.counted
        else ok := false; bad := bad + 1
      if ok then IO.println s!"  UNSAT {b}  ({gs.length} groups, dim {n})"
      else IO.println s!"  FAIL  {b}  ({bad} of {gs.length} groups not discharged, dim {n})"
      pure (ok, gs.length)

def runBridgeV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 bridge verdicts : {benchIRTableV2.length} benchmarks =="
      let mut ok := true
      let mut total := 0
      for rec in benchIRTableV2.map (fun x => suiteRecV2 x.1) ++ choiceRecsV2 do
        let (r, k) ← runBridgeBench s rec
        ok := r && ok
        total := total + k
      s.close
      let k ← RelCertifier.Verdicts.dischargedCount.get
      IO.println s!"  [bridge] {total} groups over the suite"
      let full ← RelCertifier.Verdicts.checkPhase "bridge" k expectedBridgeGroupsV2
      pure (ok && full)

end RelCertifier.VerdictsV2
