/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `grid_ffr_dos` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py grid_ffr_dos`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/grid_ffr_dos/input.txt` (do not edit). -/
def grid_ffr_dos_IRv2 : PProblem :=
  {
    name := "grid_ffr_dos"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["x", "d", "a"]
      epsilon := "0.3"
      modes := [
        {
          name := "NORMAL"
          odes := [("x", (.bin "-" (.bin "*" (.num "6.25") (.bin "-" (.bin "*" (.num "0.1") (.var "a")) (.var "d"))) (.bin "*" (.num "2.625") (.var "x")))),
            ("d", (.num "0.0")),
            ("a", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "x") (.num "-0.4")) (.cmp "<=" (.var "a") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "-2.5"))) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "x") (.num "-2.5")) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          next := ["NORMAL", "FFR"] },
        {
          name := "FFR"
          odes := [("x", (.bin "-" (.bin "*" (.num "6.25") (.bin "-" (.bin "*" (.num "0.1") (.var "a")) (.var "d"))) (.bin "*" (.num "2.625") (.var "x")))),
            ("d", (.num "0.0")),
            ("a", (.bin "*" (.num "5") (.bin "-" (.num "1") (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")) (.cmp ">=" (.var "x") (.num "-1.5"))) (.cmp ">=" (.var "x") (.num "-2.5"))) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "x") (.num "-2.5")) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          next := ["FFR"] } ] }
    R := {
      stateVars := ["x", "d", "a"]
      epsilon := "0.1"
      modes := [
        {
          name := "NORMAL"
          odes := [("x", (.bin "-" (.bin "*" (.num "6.25") (.bin "-" (.bin "*" (.num "0.1") (.var "a")) (.var "d"))) (.bin "*" (.num "2.625") (.var "x")))),
            ("d", (.num "0.0")),
            ("a", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "x") (.num "-0.4")) (.cmp "<=" (.var "a") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "-2.5"))) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "x") (.num "-2.5")) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          next := ["NORMAL", "FFR", "TRIP"] },
        {
          name := "FFR"
          odes := [("x", (.bin "-" (.bin "*" (.num "6.25") (.bin "-" (.bin "*" (.num "0.1") (.var "a")) (.var "d"))) (.bin "*" (.num "2.625") (.var "x")))),
            ("d", (.num "0.0")),
            ("a", (.bin "*" (.num "5") (.bin "-" (.num "1") (.var "a"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")) (.cmp ">=" (.var "x") (.num "-1.5"))) (.cmp ">=" (.var "x") (.num "-2.5"))) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "x") (.num "-2.5")) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          next := ["FFR", "TRIP"] },
        {
          name := "TRIP"
          odes := [("x", (.bin "*" (.num "0.5") (.bin "-" (.neg (.num "2.5")) (.var "x")))),
            ("d", (.num "0.0")),
            ("a", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "x") (.num "-1.5")) (.cmp ">=" (.var "x") (.num "-2.5"))) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "x") (.num "-2.5")) (.cmp "<=" (.var "x") (.num "1.0"))) (.cmp ">=" (.var "d") (.num "0.05"))) (.cmp "<=" (.var "d") (.num "0.3"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "1.0")))
          next := ["TRIP"] } ] }
    invariants := [
      ("NORMAL", (.and (.and (.and (.and (.cmp "<=" (.var "L_x") (.var "R_x")) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.bin "*" (.num "0.24") (.var "R_a"))))) (.cmp "<=" (.var "L_a") (.var "R_a"))) (.cmp "<=" (.var "L_d") (.var "R_d"))) (.cmp "<=" (.var "R_d") (.var "L_d")))),
      ("FFR", (.and (.and (.and (.and (.cmp "<=" (.var "L_x") (.var "R_x")) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.bin "*" (.num "0.24") (.var "R_a"))))) (.cmp "<=" (.var "L_a") (.var "R_a"))) (.cmp "<=" (.var "L_d") (.var "R_d"))) (.cmp "<=" (.var "R_d") (.var "L_d"))))] }

end RelCertifier.Parse
