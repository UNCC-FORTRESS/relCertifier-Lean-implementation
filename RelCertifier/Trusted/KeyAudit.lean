/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# W6 — the unknown-key audit gate

The trusted parser reads the keys it knows and SILENTLY DROPS the rest: a
`reset = x := 1.0` line certifies green with the reset discarded, and every suite
input carries an unread `max_depth` (docs/COVER-AUDIT.md). Editing `Trusted/Parse`
to reject would force a world rebuild (it is upstream of every emitted leaf), so
the gate lives at the CLI boundary instead: every entry point that reads a
benchmark runs `auditKeys` first and REFUSES inputs containing sections or keys
the parser does not consume. Same operational guarantee — the tool never certifies
a model containing directives it ignored — with an exe-only rebuild.

Recognized: `[problem]` name/max_depth/lambda_min/lambda_max/bound_T (max_depth
and bound_T are read by no stage and are on the explicit IGNORED list — present in
all 47 suite inputs); `[Lsys]`/`[Rsys]` state_vars/epsilon; mode sections
ode/guard/evolve/next; `[relational_invariant]` any key (keys are mode names).
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Oracle

/-- Section kinds the parser consumes. -/
private def sectionKind (s : String) : Option String :=
  if s == "problem" then some "problem"
  else if s == "Lsys" || s == "Rsys" then some "sys"
  else if s.startsWith "Lsys.mode." || s.startsWith "Rsys.mode." then some "mode"
  else if s == "relational_invariant" then some "inv"
  else none

private def knownKeys : String → List String
  | "problem" => ["name", "max_depth", "lambda_min", "lambda_max", "bound_T"]
  | "sys" => ["state_vars", "epsilon"]
  | "mode" => ["ode", "guard", "evolve", "next"]
  | _ => []

/-- Unknown sections and keys in a benchmark text: `(line, offending)` pairs. -/
def auditKeys (text : String) : List (Nat × String) := Id.run do
  let mut out : List (Nat × String) := []
  let mut kind : Option String := none
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    let s := raw.trim
    if s.isEmpty || s.startsWith "#" then
      continue
    if s.startsWith "[" && s.endsWith "]" then
      let name := ((s.drop 1).dropRight 1).toString
      match sectionKind name with
      | some k => kind := some k
      | none =>
          out := out ++ [(lineNo, s!"unknown section [{name}]")]
          kind := none
    else
      match s.splitOn "=" with
      | key :: _ :: _ =>
          let key := key.trim
          match kind with
          | some "inv" => pure ()
          | some k =>
              if !(knownKeys k).contains key then
                out := out ++ [(lineNo, s!"unknown key '{key}'")]
          | none => out := out ++ [(lineNo, s!"key '{key}' outside any known section")]
      | _ => out := out ++ [(lineNo, s!"unparsed line '{s}'")]
  return out

/-- Read + parse a benchmark, REFUSING inputs with unknown sections or keys. -/
def readProblemStrict (path : String) : IO (Except String Parse.PProblem) := do
  let txt ← IO.FS.readFile path
  let bad := auditKeys txt
  if !bad.isEmpty then
    return .error (String.intercalate "; " (bad.map (fun p =>
      s!"line {p.1}: {p.2}")) ++ " — the parser would silently drop these (W6 gate)")
  return Parse.parseProblemE txt

end RelCertifier.Oracle
