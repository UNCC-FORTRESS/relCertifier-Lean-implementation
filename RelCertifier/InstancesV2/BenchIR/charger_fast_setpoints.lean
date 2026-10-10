/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py charger_fast_setpoints`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/charger_fast_setpoints/input.txt` (do not edit). -/
def charger_fast_setpoints_IRv2 : PProblem :=
  {
    name := "charger_fast_setpoints"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["x"]
      epsilon := "2.0"
      modes := [
        {
          name := "BULK"
          odes := [("x", (.bin "*" (.num "0.125") (.bin "-" (.num "90.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "15.0")) (.cmp "<" (.var "x") (.num "80.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["ABSORB", "BULK"] },
        {
          name := "ABSORB"
          odes := [("x", (.bin "*" (.num "0.0625") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "80.0")) (.cmp "<" (.var "x") (.num "99.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL", "ABSORB"] },
        {
          name := "FULL"
          odes := [("x", (.num "0"))]
          guard := (.cmp ">=" (.var "x") (.num "99.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "BULK"
          odes := [("x", (.bin "*" (.num "0.1") (.bin "-" (.num "90.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "15.0")) (.cmp "<" (.var "x") (.num "80.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["ABSORB", "BULK", "FAULT"] },
        {
          name := "ABSORB"
          odes := [("x", (.bin "*" (.num "0.05") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "80.0")) (.cmp "<" (.var "x") (.num "99.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL", "ABSORB"] },
        {
          name := "FULL"
          odes := [("x", (.num "0"))]
          guard := (.cmp ">=" (.var "x") (.num "99.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL"] },
        {
          name := "FAULT"
          odes := [("x", (.bin "*" (.num "-0.01") (.var "x")))]
          guard := (.cmp "<" (.var "x") (.num "10.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FAULT"] } ] }
    invariants := [
      ("BULK", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "5")))),
      ("ABSORB", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "5")))),
      ("FULL", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "5"))))] }

end RelCertifier.Parse
