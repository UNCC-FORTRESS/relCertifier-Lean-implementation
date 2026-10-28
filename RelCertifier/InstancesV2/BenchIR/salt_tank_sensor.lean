/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `salt_tank_sensor` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py salt_tank_sensor`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/salt_tank_sensor/input.txt` (do not edit). -/
def salt_tank_sensor_IRv2 : PProblem :=
  {
    name := "salt_tank_sensor"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["xp"]
      epsilon := "1.0"
      modes := [
        {
          name := "On"
          odes := [("xp", (.bin "*" (.num "0.1") (.bin "-" (.num "25.0") (.var "xp"))))]
          guard := (.cmp ">=" (.var "xp") (.num "22.0"))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["On", "Off"] },
        {
          name := "Off"
          odes := [("xp", (.num "0.0"))]
          guard := (.cmp "<" (.var "xp") (.num "28.0"))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["On", "Off"] } ] }
    R := {
      stateVars := ["xp"]
      epsilon := "1.0"
      modes := [
        {
          name := "On"
          odes := [("xp", (.bin "*" (.num "0.1") (.bin "-" (.num "25.0") (.var "xp"))))]
          guard := (.cmp ">=" (.var "xp") (.num "25.0"))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["On", "Off"] },
        {
          name := "Off"
          odes := [("xp", (.num "0.0"))]
          guard := (.cmp "<" (.var "xp") (.num "25.0"))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["On", "Off"] } ] }
    invariants := [
      ("On", (.and (.and (.and (.cmp "<=" (.var "L_xp") (.bin "+" (.var "R_xp") (.num "3.0"))) (.cmp "<=" (.var "R_xp") (.bin "+" (.var "L_xp") (.num "3.0")))) (.cmp ">=" (.var "L_xp") (.num "25.0"))) (.cmp ">=" (.var "R_xp") (.num "25.0")))),
      ("Off", (.and (.and (.and (.cmp "<=" (.var "L_xp") (.bin "+" (.var "R_xp") (.num "3.0"))) (.cmp "<=" (.var "R_xp") (.bin "+" (.var "L_xp") (.num "3.0")))) (.cmp ">=" (.var "L_xp") (.num "25.0"))) (.cmp ">=" (.var "R_xp") (.num "25.0"))))] }

end RelCertifier.Parse
