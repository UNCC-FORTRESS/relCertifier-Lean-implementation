/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/watertank/input.txt` (do not edit). -/
def watertank_IRv2 : PProblem :=
  {
    name := "watertank"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "0.6") (.bin "-" (.num "15.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "5.0")) (.cmp "<" (.var "x") (.num "13.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Low", "Mid"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "0.3") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "13.0")) (.cmp "<" (.var "x") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "0.3") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.cmp ">=" (.var "x") (.num "20.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "0.3") (.bin "-" (.num "12.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "2.0")) (.cmp "<" (.var "x") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Low", "MidEco", "MidBoost", "PumpOff"] },
        {
          name := "MidEco"
          odes := [("x", (.bin "*" (.num "0.15") (.bin "-" (.num "17.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["MidEco", "MidBoost", "High"] },
        {
          name := "MidBoost"
          odes := [("x", (.bin "*" (.num "0.3") (.bin "-" (.num "17.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["MidBoost", "MidEco", "High"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "0.3") (.bin "-" (.num "17.0") (.var "x"))))]
          guard := (.cmp ">=" (.var "x") (.num "17.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "MidEco", "MidBoost"] },
        {
          name := "PumpOff"
          odes := [("x", (.num "0.0"))]
          guard := (.cmp "<" (.var "x") (.num "2.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["PumpOff"] } ] }
    invariants := [
      ("Low", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "3"))))),
      ("Mid", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "3"))))),
      ("High", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "3")))))] }

end RelCertifier.Parse
