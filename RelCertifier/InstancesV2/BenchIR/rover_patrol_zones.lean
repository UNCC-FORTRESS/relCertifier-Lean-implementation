/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_zones`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rover_patrol_zones/input.txt` (do not edit). -/
def rover_patrol_zones_IRv2 : PProblem :=
  {
    name := "rover_patrol_zones"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "2.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.bin "*" (.num "1.25") (.bin "-" (.num "0.48") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "SLOW"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.bin "*" (.num "1.25") (.bin "-" (.num "0.72") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.9")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST", "MEDIUM_BRISK", "MEDIUM_ECO"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.bin "*" (.num "1.25") (.bin "-" (.num "0.88") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.1")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST", "MEDIUM_ECO", "MEDIUM_BRISK"] },
        {
          name := "FAST"
          odes := [("v", (.bin "*" (.num "1.25") (.bin "-" (.num "1.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "50.0")) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "SLOW"
          odes := [("v", (.bin "-" (.num "0.6") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "20.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["MEDIUM_ECO", "MEDIUM_BRISK", "SLOW", "STALL"] },
        {
          name := "MEDIUM_ECO"
          odes := [("v", (.bin "-" (.num "0.9") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "0.9")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST", "MEDIUM_ECO", "STALL"] },
        {
          name := "MEDIUM_BRISK"
          odes := [("v", (.bin "-" (.num "1.1") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<" (.var "s") (.num "50.0"))) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.1")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST", "MEDIUM_BRISK", "STALL"] },
        {
          name := "FAST"
          odes := [("v", (.bin "-" (.num "1.5") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "50.0")) (.cmp ">=" (.var "v") (.num "0.3"))) (.cmp "<=" (.var "v") (.num "1.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["FAST", "STALL"] },
        {
          name := "STALL"
          odes := [("v", (.bin "*" (.num "-2.0") (.var "v"))),
            ("s", (.var "v"))]
          guard := (.cmp "<" (.var "v") (.num "0.2"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0")))
          next := ["STALL"] } ] }
    invariants := [
      ("SLOW", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.5"))))),
      ("MEDIUM_ECO", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))))),
      ("MEDIUM_BRISK", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "1.0"))))),
      ("FAST", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "2.0")))))] }

end RelCertifier.Parse
