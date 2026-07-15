/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# PProblem → Lean-literal emitter (the single-door bridge for `Faithful`)

Prints a parsed `PProblem` as a Lean term, so the benchmark IR literals checked by the
kernel-level `Faithful` certificates are EMITTED BY THE TRUSTED PARSER ITSELF, never
hand-typed. The runtime drift check (`relcert-test`) re-parses each benchmark file and
compares against the embedded literal with the derived `DecidableEq`, so a stale or
edited literal fails the battery. Round-trip property: `parse ∘ emit ∘ parse = parse`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

def qs (s : String) : String := "\"" ++ s ++ "\""

partial def emitExpr : PExpr → String
  | .var v => s!"(.var {qs v})"
  | .num c => s!"(.num {qs c})"
  | .neg a => s!"(.neg {emitExpr a})"
  | .bin op a b => s!"(.bin {qs op} {emitExpr a} {emitExpr b})"

partial def emitForm : PForm → String
  | .tt => "(.tt)"
  | .cmp op a b => s!"(.cmp {qs op} {emitExpr a} {emitExpr b})"
  | .and a b => s!"(.and {emitForm a} {emitForm b})"
  | .or a b => s!"(.or {emitForm a} {emitForm b})"
  | .not a => s!"(.not {emitForm a})"

def emitMode (m : PMode) : String :=
  let odes := String.intercalate ",\n            " (m.odes.map (fun p => "(" ++ qs p.1 ++ ", " ++ emitExpr p.2 ++ ")"))
  "        {\n          name := " ++ qs m.name
    ++ "\n          odes := [" ++ odes ++ "]"
    ++ "\n          guard := " ++ emitForm m.guard
    ++ "\n          evolve := " ++ emitForm m.evolve
    ++ "\n          next := [" ++ String.intercalate ", " (m.next.map qs) ++ "] }"

def emitSystem (sys : PSystem) : String :=
  "{\n      stateVars := [" ++ String.intercalate ", " (sys.stateVars.map qs) ++ "]"
    ++ "\n      epsilon := " ++ qs sys.epsilon
    ++ "\n      modes := [\n"
    ++ String.intercalate ",\n" (sys.modes.map emitMode) ++ " ] }"

def emitProblem (nm : String) (p : PProblem) : String :=
  let invs := String.intercalate ",\n      " (p.invariants.map (fun kv => "(" ++ qs kv.1 ++ ", " ++ emitForm kv.2 ++ ")"))
  "/-- Parser-emitted IR of `benchmarks/suite_uniform/" ++ p.name
    ++ "/input.txt` (do not edit). -/\ndef " ++ nm ++ " : PProblem :="
    ++ "\n  {\n    name := " ++ qs p.name
    ++ "\n    lambdaMin := " ++ qs p.lambdaMin
    ++ "\n    lambdaMax := " ++ qs p.lambdaMax
    ++ "\n    L := " ++ emitSystem p.L
    ++ "\n    R := " ++ emitSystem p.R
    ++ "\n    invariants := [\n      " ++ invs ++ "] }"

end RelCertifier.Parse
