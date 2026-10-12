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
    lambdaMax := "4.0"
    L := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "0.6") (.bin "-" (.num "15.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "5.0")) (.cmp "<" (.var "x") (.num "13.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Low"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Fast"
          odes := [("x", (.bin "*" (.num "0.6") (.bin "-" (.num "12.5") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "2.0")) (.cmp "<" (.var "x") (.num "8.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Fast", "Slow"] },
        {
          name := "Slow"
          odes := [("x", (.bin "*" (.num "0.2") (.bin "-" (.num "12.5") (.var "x"))))]
          guard := (.cmp ">=" (.var "x") (.num "8.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Slow"] } ] }
    invariants := [
      ("Low", (.and (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "3")))))] }

end RelCertifier.Parse
