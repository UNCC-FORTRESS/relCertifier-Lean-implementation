/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_gain_M1` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_gain_M1/input.txt` (do not edit). -/
def endurance_gain_M1_IR : PProblem :=
  {
    name := "endurance_gain_M1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45")))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45"))))] }

end RelCertifier.Parse
