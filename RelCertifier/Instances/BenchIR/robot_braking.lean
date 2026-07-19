/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `robot_braking` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/robot_braking/input.txt` (do not edit). -/
def robot_braking_IR : PProblem :=
  {
    name := "robot_braking"
    lambdaMin := "1.0"
    lambdaMax := "3.0"
    L := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "1.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.8")) (.cmp "<=" (.var "v") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["CRUISE"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "FAST"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "0.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "3.5")) (.cmp "<" (.var "v") (.num "3.55")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["MID", "FAST"] },
        {
          name := "MID"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "0.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.5")) (.cmp "<=" (.var "v") (.num "3.5")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["SLOW", "MID"] },
        {
          name := "SLOW"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "1.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.5")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["SLOW"] } ] }
    invariants := [
      ("CRUISE", (.cmp "<=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "0.5")))] }

end RelCertifier.Parse
