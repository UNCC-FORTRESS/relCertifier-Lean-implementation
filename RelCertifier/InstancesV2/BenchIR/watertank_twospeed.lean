/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank_twospeed`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/watertank_twospeed/input.txt` (do not edit). -/
def watertank_twospeed_IRv2 : PProblem :=
  {
    name := "watertank_twospeed"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "2.0") (.bin "-" (.num "15.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "5.0")) (.cmp "<" (.var "x") (.num "13.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Low", "Mid"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "1.0") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "13.0")) (.cmp "<" (.var "x") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "1.0") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.cmp ">=" (.var "x") (.num "20.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Fast"
          odes := [("x", (.bin "*" (.num "2.0") (.bin "-" (.num "12.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "2.0")) (.cmp "<" (.var "x") (.num "7.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Fast", "Slow", "MidEco", "MidBoost"] },
        {
          name := "Slow"
          odes := [("x", (.bin "*" (.num "1.0") (.bin "-" (.num "12.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "7.0")) (.cmp "<" (.var "x") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Slow", "MidEco", "MidBoost"] },
        {
          name := "MidEco"
          odes := [("x", (.bin "*" (.num "0.5") (.bin "-" (.num "17.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["MidEco", "MidBoost", "High"] },
        {
          name := "MidBoost"
          odes := [("x", (.bin "*" (.num "1.0") (.bin "-" (.num "17.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["MidBoost", "MidEco", "High"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "1.0") (.bin "-" (.num "17.0") (.var "x"))))]
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
      ("Low", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.5"))))),
      ("Mid", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.5"))))),
      ("High", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "1.5")))))] }

end RelCertifier.Parse
