/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_2to3` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_2to3`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rover_ladder_2to3/input.txt` (do not edit). -/
def rover_ladder_2to3_IRv2 : PProblem :=
  {
    name := "rover_ladder_2to3"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.cmp ">=" (.var "s") (.num "140.0"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "140.0"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi"))))),
      ("MODER", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi"))))),
      ("FLAT", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi")))))] }

end RelCertifier.Parse
