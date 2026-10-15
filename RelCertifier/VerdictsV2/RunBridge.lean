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

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Emitted RelCertifier.Progress

def coverV2 (b : String) : CoverEmitE :=
  ((coverTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, [], []⟩

def progV2 (b : String) : ProgressEmitE :=
  ((progressTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, []⟩

/-- The bridge dimension of a benchmark: the pack table's. -/
def bridgeDimV2 (b : String) : ℕ :=
  ((packsV2.find? (fun r => r.bench == b)).map (fun r => r.dim)).getD (irV2 b).L.stateVars.length

/-- Declared: the number of query groups over the suite. -/
def expectedBridgeGroupsV2 : Nat := 3259

def runBridgeBench (s : Z3Session) (b : String) : IO (Bool × Nat) := do
  let p := irV2 b
  let n := bridgeDimV2 b
  let vars := p.L.stateVars
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  match bridgeGroups p n (cutV2 b) (coverV2 b) (progV2 b) with
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
      for (b, _) in benchIRTableV2 do
        let (r, k) ← runBridgeBench s b
        ok := r && ok
        total := total + k
      s.close
      let k ← RelCertifier.Verdicts.dischargedCount.get
      IO.println s!"  [bridge] {total} groups over the suite"
      let full ← RelCertifier.Verdicts.checkPhase "bridge" k expectedBridgeGroupsV2
      pure (ok && full)

end RelCertifier.VerdictsV2
