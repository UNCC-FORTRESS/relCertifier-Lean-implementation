/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/tank_dos_3to1/input.txt` (do not edit). -/
def tank_dos_3to1_IRv2 : PProblem :=
  {
    name := "tank_dos_3to1"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["h"]
      epsilon := "3.0"
      modes := [
        {
          name := "HIGH"
          odes := [("h", (.bin "*" (.num "0.1") (.bin "-" (.num "1.3") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<" (.var "h") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["HIGH", "LOW"] },
        {
          name := "LOW"
          odes := [("h", (.bin "*" (.num "0.1") (.bin "-" (.num "0.7") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "1.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["HIGH", "LOW"] } ] }
    R := {
      stateVars := ["h"]
      epsilon := "1.0"
      modes := [
        {
          name := "HIGH"
          odes := [("h", (.bin "*" (.num "0.1") (.bin "-" (.num "1.3") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<" (.var "h") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["HIGH", "LOW"] },
        {
          name := "LOW"
          odes := [("h", (.bin "*" (.num "0.1") (.bin "-" (.num "0.7") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "1.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["HIGH", "LOW"] } ] }
    invariants := [
      ("HIGH", (.and (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.7"))) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.7"))))),
      ("LOW", (.and (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.7"))) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.7")))))] }

end RelCertifier.Parse
