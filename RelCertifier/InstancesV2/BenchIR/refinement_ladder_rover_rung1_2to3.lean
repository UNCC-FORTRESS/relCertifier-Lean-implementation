/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung1_2to3`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/refinement_ladder_rover_rung1_2to3/input.txt` (do not edit). -/
def refinement_ladder_rover_rung1_2to3_IRv2 : PProblem :=
  {
    name := "refinement_ladder_rover_rung1_2to3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

end RelCertifier.Parse
