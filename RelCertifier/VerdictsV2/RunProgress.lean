/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The progress verdict runner

Walks every emitted progress certificate (`InstancesV2/BenchProgress`), rebuilds its queries
with `progressQueriesOf` (the builder the semantic reading uses), prints them with the tool's
`toScript`, and owes one `unsat` per query. The total number of certificates is declared
(`expectedProgressV2`); anything that cannot be rebuilt is a SKIP and makes the run non-green.
-/
import RelCertifier.VerdictsV2.ProgressX
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.InstancesV2.BenchProgress

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Oracle RelCertifier.Progress

/-- The emitted certificates of the suite (one row per certificate). -/
def expectedProgressV2 : Nat :=
  progressTableV2.foldl (fun k p => k + p.2.certs.length) 0

def runProgressCert (s : Z3Session) (b : String) (c : ProgressE) : IO Bool := do
  let p := irV2 b
  let cX := cutV2 b
  let vars := p.L.stateVars
  let n := vars.length
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  let l := modeIdx p.L.modes c.mL
  let m := modeIdx p.R.modes c.mR
  -- exactly the queries `ProgressVerd` quantifies over
  match progressQueriesOf p cX n (invRowOf p l) l m c with
  | none =>
      IO.println s!"  SKIP  {b} {c.mL}_L/{c.mR} pre={c.pre} (rebuild failed)"
      pure false
  | some qs =>
      let mut ok := true
      let mut detail := ""
      for q in qs do
        match ← s.check (q.toScript coord) with
        | .ok .unsat => detail := detail ++ "u"
        | .ok .sat => detail := detail ++ "S"; ok := false
        | .ok _ => detail := detail ++ "?"; ok := false
        | .error _ => detail := detail ++ "E"; ok := false
      if ok then
        IO.println s!"  UNSAT ({qs.length}: {detail})  {b} {c.mL}_L/{c.mR} pre={c.pre}"
        RelCertifier.Verdicts.counted
      else
        IO.println s!"  FAIL  ({detail})  {b} {c.mL}_L/{c.mR} pre={c.pre}"
      pure ok

def runProgressV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 progress certificates : {expectedProgressV2} =="
      let mut ok := true
      for (b, e) in progressTableV2 do
        for c in e.certs do
          ok := (← runProgressCert s b c) && ok
      s.close
      let k ← RelCertifier.Verdicts.dischargedCount.get
      let full ← RelCertifier.Verdicts.checkPhase "progress" k expectedProgressV2
      pure (ok && full)

end RelCertifier.VerdictsV2
