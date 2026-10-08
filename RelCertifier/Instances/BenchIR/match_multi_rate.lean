/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/match_multi_rate/input.txt` (do not edit). -/
def match_multi_rate_IR : PProblem :=
  {
    name := "match_multi_rate"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "FAST"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.2")) (.cmp "<" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["MEDIUM", "FAST"] },
        {
          name := "MEDIUM"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.5")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["SLOW", "MEDIUM"] },
        {
          name := "SLOW"
          odes := [("v", (.bin "*" (.num "1") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.7")) (.cmp "<=" (.var "v") (.num "0.95")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["RESET", "SLOW"] },
        {
          name := "RESET"
          odes := [("v", (.bin "*" (.num "4") (.bin "-" (.num "0.1") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.95")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["FAST", "RESET"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "DRIVE"
          odes := [("v", (.bin "*" (.num "1") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.2")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["DRIVE", "STALL"] },
        {
          name := "STALL"
          odes := [("v", (.bin "*" (.num "-2") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.cmp "<" (.var "v") (.num "0.2"))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["STALL"] } ] }
    invariants := [
      ("FAST", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("MEDIUM", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("SLOW", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("RESET", (.cmp "<=" (.var "L_v") (.var "R_v")))] }

end RelCertifier.Parse
