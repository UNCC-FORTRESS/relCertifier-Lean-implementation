/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The refutation verdict runner (branch `refutation`)

Per refutation record (`InstancesV2/Refute/Table.lean`), every group of `Emitted.refGroups`
(the no-partner queries of kind C, the rigidity queries of kind A, one per right mode) is sent
to Z3; a group is discharged when its member is `unsat`. The groups are exactly the queries
`Emitted.RefVerdicts` reads, the hypothesis of each instance's `refuted`; so the runner's green
light (with the declared total met) is that hypothesis.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteData
import RelCertifier.InstancesV2.Refute.Table
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Oracle RelCertifier.Emitted RelCertifier.Refute

def runRefuteOne (s : Z3Session) (r : RefRec) : IO (Bool × Nat) := do
  let n := r.dim
  let vars := r.ir.L.stateVars
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  match refGroups r.ir n r.cuts r.wit with
  | none =>
      IO.println s!"  FAIL  {r.name}  (the query groups did not rebuild)"
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
      if ok then IO.println s!"  UNSAT {r.name}  (kind {r.wit.kind}, {gs.length} groups, dim {n})"
      else IO.println s!"  FAIL  {r.name}  ({bad} of {gs.length} groups not discharged, dim {n})"
      pure (ok, gs.length)

def runRefuteV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== refutation verdicts : {refuteTable.length} mutants =="
      let mut ok := true
      let mut total := 0
      for rec in refuteTable do
        let (r, k) ← runRefuteOne s rec
        ok := r && ok
        total := total + k
      s.close
      let k ← RelCertifier.Verdicts.dischargedCount.get
      IO.println s!"  [refute] {total} groups over the refutations"
      let full ← RelCertifier.Verdicts.checkPhase "refute" k expectedRefuteGroups
      pure (ok && full)

end RelCertifier.VerdictsV2
