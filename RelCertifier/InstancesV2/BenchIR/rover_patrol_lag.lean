/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_lag` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_lag`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rover_patrol_lag/input.txt` (do not edit). -/
def rover_patrol_lag_IRv2 : PProblem :=
  {
    name := "rover_patrol_lag"
    lambdaMin := "1.0"
    lambdaMax := "1.5"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "0.6") (.var "v")) (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "0.9") (.var "v")) (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "1.1") (.var "v")) (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_BRISK", "MEDIUM_ECO", "FAST"] },
        {
          name := "FAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "1.5") (.var "v")) (.var "a"))))]
          guard := (.cmp ">=" (.var "s") (.num "50.0"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.bin "-" (.num "0.6") (.var "v"))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.bin "-" (.num "0.9") (.var "v"))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.bin "-" (.num "1.1") (.var "v"))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_BRISK", "MEDIUM_ECO", "FAST"] },
        {
          name := "FAST"
          odes := [("v", (.bin "-" (.num "1.5") (.var "v"))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "50.0"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST"] } ] }
    invariants := [
      ("SLOW", (.and (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.var "L_v")) (.bin "*" (.num "0.1875") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.num "0.375"))))),
      ("MEDIUM_ECO", (.and (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.var "L_v")) (.bin "*" (.num "0.1875") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.num "0.375"))))),
      ("MEDIUM_BRISK", (.and (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.var "L_v")) (.bin "*" (.num "0.1875") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.num "0.375"))))),
      ("FAST", (.and (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.var "L_v")) (.bin "*" (.num "0.1875") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.num "0.375")))))] }

end RelCertifier.Parse
