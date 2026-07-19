/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_orderlift_2to3` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_orderlift_2to3/input.txt` (do not edit). -/
def endurance_orderlift_2to3_IR : PProblem :=
  {
    name := "endurance_orderlift_2to3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a", "j"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "14.40") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "24.00") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "31.20") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.67")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "a", "j"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "4.80") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "8.00") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "10.40") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "FLAT", "STEEP"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411"))))),
      ("MODER", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411"))))),
      ("FLAT", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411")))))] }

end RelCertifier.Parse
