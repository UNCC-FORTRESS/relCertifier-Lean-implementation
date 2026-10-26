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
          name := "PUMP_ON"
          odes := [("h", (.bin "*" (.num "0.1") (.bin "-" (.num "1.6") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<" (.var "h") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["PUMP_ON", "PUMP_OFF"] },
        {
          name := "PUMP_OFF"
          odes := [("h", (.bin "*" (.num "-0.1") (.var "h")))]
          guard := (.and (.cmp ">=" (.var "h") (.num "1.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["PUMP_ON", "PUMP_OFF"] } ] }
    R := {
      stateVars := ["h"]
      epsilon := "1.0"
      modes := [
        {
          name := "MODULATE"
          odes := [("h", (.bin "*" (.num "0.2") (.bin "-" (.num "1.0") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.4")) (.cmp "<=" (.var "h") (.num "2.0")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.4")) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["MODULATE"] } ] }
    invariants := [
      ("PUMP_ON", (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.75")))),
      ("PUMP_OFF", (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.75"))))] }

end RelCertifier.Parse
