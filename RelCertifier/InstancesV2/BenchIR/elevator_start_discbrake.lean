/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `elevator_start_discbrake` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py elevator_start_discbrake`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/elevator_start_discbrake/input.txt` (do not edit). -/
def elevator_start_discbrake_IRv2 : PProblem :=
  {
    name := "elevator_start_discbrake"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["z", "v", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "LIFT"
          odes := [("z", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "50.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "z") (.num "0.1")) (.cmp "<=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "b") (.num "0.95"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["LIFT", "UP"] },
        {
          name := "UP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.num "0.8") (.bin "-" (.num "1.6") (.var "v")))),
            ("b", (.bin "*" (.num "50.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "z") (.num "18.0")) (.cmp ">=" (.var "b") (.num "0.95"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["UP", "APP"] },
        {
          name := "APP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.num "0.8") (.bin "-" (.num "0.25") (.var "v")))),
            ("b", (.bin "*" (.num "50.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "18.0")) (.cmp "<" (.var "z") (.num "19.9"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["APP", "STOP"] },
        {
          name := "STOP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.neg (.num "4.0")) (.var "v"))),
            ("b", (.bin "*" (.neg (.num "5.0")) (.var "b")))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "19.9")) (.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["z", "v", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "LIFT"
          odes := [("z", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "5.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "z") (.num "0.1")) (.cmp "<=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "b") (.num "0.95"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["LIFT", "UP"] },
        {
          name := "UP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.num "0.8") (.bin "-" (.num "1.6") (.var "v")))),
            ("b", (.bin "*" (.num "5.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "z") (.num "18.0")) (.cmp ">=" (.var "b") (.num "0.95"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["UP", "APP"] },
        {
          name := "APP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.num "0.8") (.bin "-" (.num "0.25") (.var "v")))),
            ("b", (.bin "*" (.num "5.0") (.bin "-" (.num "1.0") (.var "b"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "18.0")) (.cmp "<" (.var "z") (.num "19.9"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["APP", "STOP"] },
        {
          name := "STOP"
          odes := [("z", (.var "v")),
            ("v", (.bin "*" (.neg (.num "4.0")) (.var "v"))),
            ("b", (.bin "*" (.neg (.num "5.0")) (.var "b")))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "19.9")) (.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5"))) (.cmp ">=" (.var "z") (.num "-0.5"))) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "z") (.num "-0.5")) (.cmp "<=" (.var "z") (.num "20.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.7"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.0")))
          next := ["STOP"] } ] }
    invariants := [
      ("LIFT", (.and (.and (.and (.and (.cmp "<=" (.var "L_z") (.var "R_z")) (.cmp "<=" (.var "R_z") (.var "L_z"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("UP", (.and (.and (.and (.cmp "<=" (.var "L_z") (.var "R_z")) (.cmp "<=" (.var "R_z") (.var "L_z"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("APP", (.and (.and (.and (.cmp "<=" (.var "L_z") (.var "R_z")) (.cmp "<=" (.var "R_z") (.var "L_z"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("STOP", (.and (.and (.and (.cmp "<=" (.var "L_z") (.var "R_z")) (.cmp "<=" (.var "R_z") (.var "L_z"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))))] }

end RelCertifier.Parse
