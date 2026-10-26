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
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "2.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "1.25") (.bin "-" (.num "0.48") (.var "v"))) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.6"))) (.cmp ">=" (.var "a") (.num "-0.5"))) (.cmp "<=" (.var "a") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "SLOW"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "1.25") (.bin "-" (.num "0.72") (.var "v"))) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.9"))) (.cmp ">=" (.var "a") (.num "-0.5"))) (.cmp "<=" (.var "a") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST", "MEDIUM_BRISK", "MEDIUM_ECO"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "1.25") (.bin "-" (.num "0.88") (.var "v"))) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.1"))) (.cmp ">=" (.var "a") (.num "-0.5"))) (.cmp "<=" (.var "a") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST", "MEDIUM_ECO", "MEDIUM_BRISK"] },
        {
          name := "FAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "*" (.num "1.25") (.bin "-" (.num "1.20") (.var "v"))) (.var "a"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "50.0")) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.5"))) (.cmp ">=" (.var "a") (.num "-0.5"))) (.cmp "<=" (.var "a") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "0.6") (.var "v")) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "a") (.neg (.num "2.0")))) (.cmp "<=" (.var "a") (.num "2.0"))) (.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.neg (.num "0.3")))) (.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.num "7.5"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "0.7"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "6.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "SLOW"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "0.9") (.var "v")) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "a") (.neg (.num "2.0")))) (.cmp "<=" (.var "a") (.num "2.0"))) (.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.neg (.num "0.3")))) (.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.num "7.5"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "0.7"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "6.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST", "MEDIUM_ECO"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "1.1") (.var "v")) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "a") (.neg (.num "2.0")))) (.cmp "<=" (.var "a") (.num "2.0"))) (.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.neg (.num "0.3")))) (.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.num "7.5"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "0.7"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "6.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST", "MEDIUM_BRISK"] },
        {
          name := "FAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.bin "/" (.num "16.0") (.num "3.0")) (.bin "-" (.bin "-" (.num "1.5") (.var "v")) (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "50.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "a") (.neg (.num "2.0")))) (.cmp "<=" (.var "a") (.num "2.0"))) (.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.neg (.num "0.3")))) (.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "4.0") (.var "v"))) (.num "7.5"))) (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "0.7"))) (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "4.0") (.var "v"))) (.num "6.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "2.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "a") (.num "-2.0"))) (.cmp "<=" (.var "a") (.num "2.0")))
          next := ["FAST"] } ] }
    invariants := [
      ("SLOW", (.and (.and (.cmp "<=" (.bin "+" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_v") (.bin "*" (.num "0.25") (.var "R_a"))) (.num "0.3"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.bin "*" (.num "0.8") (.var "L_v"))) (.bin "*" (.num "0.15") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.bin "*" (.num "0.1875") (.var "R_a"))))) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))))),
      ("MEDIUM_ECO", (.and (.and (.cmp "<=" (.bin "+" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_v") (.bin "*" (.num "0.25") (.var "R_a"))) (.num "0.3"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.bin "*" (.num "0.8") (.var "L_v"))) (.bin "*" (.num "0.15") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.bin "*" (.num "0.1875") (.var "R_a"))))) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))))),
      ("MEDIUM_BRISK", (.and (.and (.cmp "<=" (.bin "+" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_v") (.bin "*" (.num "0.25") (.var "R_a"))) (.num "0.3"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.bin "*" (.num "0.8") (.var "L_v"))) (.bin "*" (.num "0.15") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.bin "*" (.num "0.1875") (.var "R_a"))))) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))))),
      ("FAST", (.and (.and (.cmp "<=" (.bin "+" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_v") (.bin "*" (.num "0.25") (.var "R_a"))) (.num "0.3"))) (.cmp "<=" (.bin "+" (.bin "+" (.var "L_s") (.bin "*" (.num "0.8") (.var "L_v"))) (.bin "*" (.num "0.15") (.var "L_a"))) (.bin "+" (.bin "+" (.var "R_s") (.var "R_v")) (.bin "*" (.num "0.1875") (.var "R_a"))))) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0")))))] }

end RelCertifier.Parse
