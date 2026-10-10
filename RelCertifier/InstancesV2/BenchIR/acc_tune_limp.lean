/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_tune_limp`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/acc_tune_limp/input.txt` (do not edit). -/
def acc_tune_limp_IRv2 : PProblem :=
  {
    name := "acc_tune_limp"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.bin "*" (.num "0.75") (.bin "-" (.num "30.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "22.0")) (.cmp "<=" (.var "v") (.num "36.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["CRUISE", "LIMP"] },
        {
          name := "LIMP"
          odes := [("v", (.bin "*" (.num "0.3") (.bin "-" (.num "25.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "22.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["LIMP"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<=" (.var "v") (.num "36.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["NORMAL", "COMFORT", "SPORT", "DISENGAGE"] },
        {
          name := "COMFORT"
          odes := [("v", (.bin "*" (.num "0.4") (.bin "-" (.num "30.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<=" (.var "v") (.num "36.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["COMFORT", "NORMAL", "DISENGAGE"] },
        {
          name := "SPORT"
          odes := [("v", (.bin "*" (.num "0.6") (.bin "-" (.num "30.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<=" (.var "v") (.num "36.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["SPORT", "NORMAL", "DISENGAGE"] },
        {
          name := "DISENGAGE"
          odes := [("v", (.bin "*" (.num "-0.5") (.var "v")))]
          guard := (.cmp "<" (.var "v") (.num "20.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["DISENGAGE"] } ] }
    invariants := [
      ("CRUISE", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "2.0"))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "2.0"))))),
      ("LIMP", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "2.0"))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "6.5")))))] }

end RelCertifier.Parse
