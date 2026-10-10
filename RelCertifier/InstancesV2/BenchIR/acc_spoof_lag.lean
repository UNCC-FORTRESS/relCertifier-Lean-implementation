/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_lag` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_spoof_lag`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/acc_spoof_lag/input.txt` (do not edit). -/
def acc_spoof_lag_IRv2 : PProblem :=
  {
    name := "acc_spoof_lag"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "a"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.var "a")),
            ("a", (.bin "*" (.num "2.5") (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.bin "*" (.num "1.25") (.var "v")))) (.var "a"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "v") (.num "23.0")) (.cmp "<=" (.var "v") (.num "30.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0"))) (.cmp ">=" (.var "a") (.num "-10.0"))) (.cmp "<=" (.var "a") (.num "10.0")))
          next := ["CRUISE"] } ] }
    R := {
      stateVars := ["v", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.var "v")))),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<" (.var "v") (.num "40.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0"))) (.cmp ">=" (.var "a") (.num "-10.0"))) (.cmp "<=" (.var "a") (.num "10.0")))
          next := ["CRUISE", "DISENGAGE"] },
        {
          name := "DISENGAGE"
          odes := [("v", (.bin "*" (.num "-0.5") (.var "v"))),
            ("a", (.num "0"))]
          guard := (.cmp "<" (.var "v") (.num "20.0"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0"))) (.cmp ">=" (.var "a") (.num "-10.0"))) (.cmp "<=" (.var "a") (.num "10.0")))
          next := ["DISENGAGE"] } ] }
    invariants := [
      ("CRUISE", (.cmp "<=" (.bin "+" (.var "L_a") (.bin "*" (.num "2.5") (.var "L_v"))) (.bin "-" (.bin "*" (.num "2.5") (.var "R_v")) (.num "5.5"))))] }

end RelCertifier.Parse
