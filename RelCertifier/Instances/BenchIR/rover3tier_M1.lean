/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_M1` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_patrol_simple/input.txt` (do not edit). -/
def rover3tier_M1_IR : PProblem :=
  {
    name := "rover_patrol_simple"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "1.5") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.05")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["ACCEL", "COAST"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["ACCEL", "COAST"] } ] }
    invariants := [
      ("ACCEL", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5")))),
      ("COAST", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5"))))] }

end RelCertifier.Parse
