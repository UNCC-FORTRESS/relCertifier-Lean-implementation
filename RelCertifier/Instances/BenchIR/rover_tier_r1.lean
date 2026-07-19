/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_r1` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_tier_r1/input.txt` (do not edit). -/
def rover_tier_r1_IR : PProblem :=
  {
    name := "rover_tier_r1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["s", "v", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("s", (.var "v")),
            ("v", (.var "a")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "0.4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<=" (.var "v") (.num "1.21")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "0.55"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.25"))) (.cmp "<=" (.var "v") (.num "1.4")))
          next := ["Cruise"] } ] }
    R := {
      stateVars := ["s", "v", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("s", (.var "v")),
            ("v", (.var "a")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.cmp ">=" (.var "v") (.num "0.3"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.3")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.25")))
          next := ["Cruise"] } ] }
    invariants := [
      ("Cruise", (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.5"))))] }

end RelCertifier.Parse
