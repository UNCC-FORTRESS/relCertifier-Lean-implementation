/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The verdict runner (`--run-verdicts`)

Executes the IR mirrors of every theorem-hypothesis query through the SAME printer
(`toScript`) and a live Z3 session, reporting per hypothesis which route returned
`unsat`. The kernel identity theorems (`Verdicts/<bench>.lean`) guarantee the printed
queries are exactly the hypothesized ones; an all-green run is the empirical record
that every theorem's Z3 hypotheses hold (docs/VERDICTS.md).
-/
import RelCertifier.Verdicts.Watertank
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.WatertankVerdicts

def wtCoord : Fin 2 → String := fun i => ["x", "pad"].getD i.val "pad"

def watertankPairs : List (String × ℕ × ℕ) :=
  [("watertank window Low  / right Low ", 0, 0),
   ("watertank window Low  / right Mid ", 0, 1),
   ("watertank window Mid  / right Mid ", 1, 1),
   ("watertank window High / right Low ", 2, 0),
   ("watertank window High / right Mid ", 2, 1),
   ("watertank window High / right High", 2, 2)]

def checkOne (s : Z3Session) (nm : String) (l q : ℕ) : IO Bool := do
  let routes : List (String × IForm 2) :=
    [("A", wtA l q), ("B", wtB l q), ("C", wtC l q)]
  for (rn, f) in routes do
    match ← s.check (f.toScript wtCoord) with
    | .ok .unsat =>
        IO.println s!"  UNSAT (route {rn})  {nm}"
        counted
        return true
    | _ => pure ()
  IO.println s!"  FAIL  {nm}  (no route unsat)"
  return false

def runVerdicts (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println "== watertank_modal_certified : 6 VerdW hypotheses =="
      let mut ok := true
      for (nm, l, q) in watertankPairs do
        ok := (← checkOne s nm l q) && ok
      s.close
      pure ok

end RelCertifier.Verdicts
