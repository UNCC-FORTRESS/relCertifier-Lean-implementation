/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `gantry_speed_zones` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py gantry_speed_zones`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/gantry_speed_zones/input.txt` (do not edit). -/
def gantry_speed_zones_IRv2 : PProblem :=
  {
    name := "gantry_speed_zones"
    lambdaMin := "1.0"
    lambdaMax := "3.0"
    L := {
      stateVars := ["x", "y"]
      epsilon := "0.1"
      modes := [
        {
          name := "FREE"
          odes := [("x", (.bin "*" (.num "6.0") (.bin "-" (.num "0.5") (.var "x")))),
            ("y", (.bin "*" (.num "3.0") (.bin "-" (.num "0.3") (.var "y"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<" (.var "x") (.num "0.3"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          next := ["FREE", "APPROACH"] },
        {
          name := "APPROACH"
          odes := [("x", (.bin "*" (.num "4.0") (.bin "-" (.num "0.5") (.var "x")))),
            ("y", (.bin "*" (.num "2.0") (.bin "-" (.num "0.3") (.var "y"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.3")) (.cmp "<" (.var "x") (.num "0.45"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          next := ["APPROACH", "PLACE"] },
        {
          name := "PLACE"
          odes := [("x", (.bin "*" (.num "2.0") (.bin "-" (.num "0.5") (.var "x")))),
            ("y", (.bin "*" (.num "1.0") (.bin "-" (.num "0.3") (.var "y"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.45")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          next := ["PLACE"] } ] }
    R := {
      stateVars := ["x", "y"]
      epsilon := "0.1"
      modes := [
        {
          name := "MOVE"
          odes := [("x", (.bin "*" (.num "2.0") (.bin "-" (.num "0.5") (.var "x")))),
            ("y", (.bin "*" (.num "1.0") (.bin "-" (.num "0.3") (.var "y"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.5")))
          next := ["MOVE"] } ] }
    invariants := [
      ("FREE", (.and (.and (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.01"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.01")))) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.01")))) (.cmp "<=" (.var "R_y") (.bin "+" (.var "L_y") (.num "0.01"))))),
      ("APPROACH", (.and (.and (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.01"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.01")))) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.01")))) (.cmp "<=" (.var "R_y") (.bin "+" (.var "L_y") (.num "0.01"))))),
      ("PLACE", (.and (.and (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.01"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.01")))) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.01")))) (.cmp "<=" (.var "R_y") (.bin "+" (.var "L_y") (.num "0.01")))))] }

end RelCertifier.Parse
