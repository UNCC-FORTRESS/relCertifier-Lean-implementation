/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_lz21_vehicle_position` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_lz21_vehicle_position`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/lit_lz21_vehicle_position/input.txt` (do not edit). -/
def lit_lz21_vehicle_position_IRv2 : PProblem :=
  {
    name := "lit_lz21_vehicle_position"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["x", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Um"
          odes := [("x", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.05")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.05")) (.cmp "<=" (.var "v") (.num "0.1")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] },
        {
          name := "U0"
          odes := [("x", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.1")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] },
        {
          name := "Up"
          odes := [("x", (.var "v")),
            ("v", (.num "0.05"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.05")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] } ] }
    R := {
      stateVars := ["x", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Um"
          odes := [("x", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.05")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.05")) (.cmp "<=" (.var "v") (.num "0.1")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] },
        {
          name := "U0"
          odes := [("x", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.1")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] },
        {
          name := "Up"
          odes := [("x", (.var "v")),
            ("v", (.num "0.05"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.05")))
          evolve := (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.1")))
          next := ["Um", "U0", "Up"] } ] }
    invariants := [
      ("Um", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp ">=" (.var "R_x") (.num "1.0"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "1.0")))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.0"))))),
      ("U0", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp ">=" (.var "R_x") (.num "1.0"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "1.0")))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.0"))))),
      ("Up", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp ">=" (.var "R_x") (.num "1.0"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "1.0")))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.0")))))] }

end RelCertifier.Parse
