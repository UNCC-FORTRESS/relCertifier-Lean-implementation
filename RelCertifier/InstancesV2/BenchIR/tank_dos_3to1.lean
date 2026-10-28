/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/tank_dos_3to1/input.txt` (do not edit). -/
def tank_dos_3to1_IRv2 : PProblem :=
  {
    name := "tank_dos_3to1"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["h", "w"]
      epsilon := "30.0"
      modes := [
        {
          name := "P2"
          odes := [("h", (.bin "-" (.bin "*" (.num "2.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "6.0")) (.cmp "<" (.var "w") (.num "10.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P2", "P3", "P4", "P5"] },
        {
          name := "P3"
          odes := [("h", (.bin "-" (.bin "*" (.num "3.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "10.0")) (.cmp "<" (.var "w") (.num "14.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P3", "P4", "P5"] },
        {
          name := "P4"
          odes := [("h", (.bin "-" (.bin "*" (.num "4.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "14.0")) (.cmp "<" (.var "w") (.num "18.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P4", "P5"] },
        {
          name := "P5"
          odes := [("h", (.bin "-" (.bin "*" (.num "5.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "18.0")) (.cmp "<=" (.var "w") (.num "22.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P5"] } ] }
    R := {
      stateVars := ["h", "w"]
      epsilon := "10.0"
      modes := [
        {
          name := "P2"
          odes := [("h", (.bin "-" (.bin "*" (.num "2.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "6.0")) (.cmp "<" (.var "w") (.num "10.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P2", "P3"] },
        {
          name := "P3"
          odes := [("h", (.bin "-" (.bin "*" (.num "3.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "10.0")) (.cmp "<" (.var "w") (.num "14.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P3", "P4"] },
        {
          name := "P4"
          odes := [("h", (.bin "-" (.bin "*" (.num "4.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "14.0")) (.cmp "<" (.var "w") (.num "18.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P4", "P5"] },
        {
          name := "P5"
          odes := [("h", (.bin "-" (.bin "*" (.num "5.0") (.num "0.005")) (.bin "*" (.num "0.001") (.bin "*" (.var "w") (.var "h"))))),
            ("w", (.bin "*" (.num "0.02") (.bin "-" (.num "22.0") (.var "w"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "18.0")) (.cmp "<=" (.var "w") (.num "22.0"))) (.cmp ">=" (.var "h") (.num "0.0"))) (.cmp "<=" (.var "h") (.num "2.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.5"))) (.cmp ">=" (.var "w") (.num "6.0"))) (.cmp "<=" (.var "w") (.num "22.0")))
          next := ["P5"] } ] }
    invariants := [
      ("P2", (.and (.and (.and (.cmp "<=" (.var "L_h") (.var "R_h")) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.8")))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_w") (.var "L_w")))),
      ("P3", (.and (.and (.and (.cmp "<=" (.var "L_h") (.var "R_h")) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.8")))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_w") (.var "L_w")))),
      ("P4", (.and (.and (.and (.cmp "<=" (.var "L_h") (.var "R_h")) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.8")))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_w") (.var "L_w")))),
      ("P5", (.and (.and (.and (.cmp "<=" (.var "L_h") (.var "R_h")) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.8")))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_w") (.var "L_w"))))] }

end RelCertifier.Parse
