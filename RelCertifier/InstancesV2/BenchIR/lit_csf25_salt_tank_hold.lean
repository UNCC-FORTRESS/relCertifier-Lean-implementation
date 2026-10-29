/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_csf25_salt_tank_hold`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/lit_csf25_salt_tank_hold/input.txt` (do not edit). -/
def lit_csf25_salt_tank_hold_IRv2 : PProblem :=
  {
    name := "lit_csf25_salt_tank_hold"
    lambdaMin := "0.3333333333"
    lambdaMax := "1.0"
    L := {
      stateVars := ["xp", "t"]
      epsilon := "3.0"
      modes := [
        {
          name := "HoldInc"
          odes := [("xp", (.bin "*" (.num "0.03") (.bin "-" (.num "100.0") (.var "xp")))),
            ("t", (.num "1.0"))]
          guard := (.and (.and (.cmp "<" (.var "xp") (.num "35.0")) (.cmp ">=" (.var "t") (.num "5.0"))) (.cmp "<=" (.var "t") (.num "5.0")))
          evolve := (.and (.cmp ">=" (.var "xp") (.num "0.0")) (.cmp "<=" (.var "xp") (.num "300.0")))
          next := ["HoldInc"] },
        {
          name := "HoldDec"
          odes := [("xp", (.bin "*" (.num "0.03") (.bin "-" (.num "25.0") (.var "xp")))),
            ("t", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "xp") (.num "35.0")) (.cmp ">=" (.var "t") (.num "5.0"))) (.cmp "<=" (.var "t") (.num "5.0")))
          evolve := (.and (.cmp ">=" (.var "xp") (.num "0.0")) (.cmp "<=" (.var "xp") (.num "300.0")))
          next := ["HoldDec"] } ] }
    R := {
      stateVars := ["xp", "t"]
      epsilon := "1.0"
      modes := [
        {
          name := "Inc"
          odes := [("xp", (.bin "*" (.num "0.03") (.bin "-" (.num "100.0") (.var "xp")))),
            ("t", (.num "1.0"))]
          guard := (.cmp "<" (.var "xp") (.num "35.0"))
          evolve := (.and (.cmp ">=" (.var "xp") (.num "0.0")) (.cmp "<=" (.var "xp") (.num "300.0")))
          next := ["Inc", "Dec"] },
        {
          name := "Dec"
          odes := [("xp", (.bin "*" (.num "0.03") (.bin "-" (.num "25.0") (.var "xp")))),
            ("t", (.num "1.0"))]
          guard := (.cmp ">=" (.var "xp") (.num "35.0"))
          evolve := (.and (.cmp ">=" (.var "xp") (.num "0.0")) (.cmp "<=" (.var "xp") (.num "300.0")))
          next := ["Inc", "Dec"] } ] }
    invariants := [
      ("HoldInc", (.and (.and (.cmp "<=" (.var "R_xp") (.var "L_xp")) (.cmp "<=" (.var "L_xp") (.bin "-" (.bin "+" (.var "R_xp") (.bin "*" (.var "L_t") (.num "1.31"))) (.num "6.55")))) (.cmp ">=" (.var "R_xp") (.num "34.5")))),
      ("HoldDec", (.and (.and (.cmp "<=" (.var "L_xp") (.var "R_xp")) (.cmp "<=" (.var "R_xp") (.bin "-" (.bin "+" (.var "L_xp") (.bin "*" (.var "L_t") (.num "0.25"))) (.num "1.25")))) (.cmp "<=" (.var "R_xp") (.num "37.1"))))] }

end RelCertifier.Parse
