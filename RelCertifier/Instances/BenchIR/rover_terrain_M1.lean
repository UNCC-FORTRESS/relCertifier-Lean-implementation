/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_M1` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_terrain_M1/input.txt` (do not edit). -/
def rover_terrain_M1_IR : PProblem :=
  {
    name := "rover_terrain_M1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "ROUGH"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.4") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "ROUGH"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.8") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["ROUGH", "SMOOTH", "FLAT"] },
        {
          name := "SMOOTH"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "1.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.25")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "SMOOTH"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.5"
      modes := [
        {
          name := "ROUGH"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.4") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "ROUGH"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.8") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["ROUGH", "SMOOTH", "FLAT"] },
        {
          name := "SMOOTH"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.25")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "SMOOTH"] } ] }
    invariants := [
      ("ROUGH", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2")))),
      ("SMOOTH", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2"))))] }

end RelCertifier.Parse
