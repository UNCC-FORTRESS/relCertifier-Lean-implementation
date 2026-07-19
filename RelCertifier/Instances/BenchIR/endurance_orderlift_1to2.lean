/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_orderlift_1to2` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_orderlift_1to2/input.txt` (do not edit). -/
def endurance_orderlift_1to2_IR : PProblem :=
  {
    name := "endurance_orderlift_1to2"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "4.80") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "8.00") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "10.40") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "FLAT", "STEEP"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3")))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3"))))] }

end RelCertifier.Parse
