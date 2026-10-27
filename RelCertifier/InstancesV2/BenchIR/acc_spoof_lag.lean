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
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "a"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.var "a")),
            ("a", (.bin "*" (.bin "/" (.num "8.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.bin "*" (.num "1.25") (.var "v")))) (.var "a"))))]
          guard := (.and (.and (.and (.cmp ">=" (.bin "+" (.var "a") (.bin "-" (.var "v") (.num "24.0"))) (.neg (.num "3.0"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "-" (.var "v") (.num "24.0"))) (.num "8.0"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.bin "/" (.num "5.0") (.num "3.0")) (.bin "-" (.var "v") (.num "24.0")))) (.neg (.bin "/" (.num "11.0") (.num "3.0"))))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.bin "/" (.num "5.0") (.num "3.0")) (.bin "-" (.var "v") (.num "24.0")))) (.num "12.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0"))) (.cmp ">=" (.var "a") (.num "-10.0"))) (.cmp "<=" (.var "a") (.num "10.0")))
          next := ["CRUISE"] } ] }
    R := {
      stateVars := ["v", "a"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.var "a")),
            ("a", (.bin "*" (.bin "/" (.num "8.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.var "v"))) (.var "a"))))]
          guard := (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "40.0")) (.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "66.0"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "44.0"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "62.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0"))) (.cmp ">=" (.var "a") (.num "-10.0"))) (.cmp "<=" (.var "a") (.num "10.0")))
          next := ["CRUISE"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.bin "+" (.var "L_v") (.bin "*" (.num "0.5") (.var "L_a"))) (.bin "+" (.var "R_v") (.bin "*" (.num "0.5") (.var "R_a"))))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "8.0")))) (.cmp "<=" (.bin "+" (.var "R_v") (.bin "*" (.num "0.5") (.var "R_a"))) (.bin "+" (.bin "+" (.var "L_v") (.bin "*" (.num "0.5") (.var "L_a"))) (.num "8.0")))))] }

end RelCertifier.Parse
