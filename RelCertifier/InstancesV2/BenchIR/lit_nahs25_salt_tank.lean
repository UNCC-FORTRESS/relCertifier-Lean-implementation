/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_salt_tank` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_salt_tank`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/lit_nahs25_salt_tank/input.txt` (do not edit). -/
def lit_nahs25_salt_tank_IRv2 : PProblem :=
  {
    name := "lit_nahs25_salt_tank"
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
      ("On", (.and (.and (.and (.cmp "<=" (.var "L_xp") (.bin "+" (.var "R_xp") (.num "0.0"))) (.cmp "<=" (.var "R_xp") (.bin "+" (.var "L_xp") (.num "0.0")))) (.cmp ">=" (.var "L_xp") (.num "25.0"))) (.cmp ">=" (.var "R_xp") (.num "25.0")))),
      ("Off", (.and (.and (.and (.cmp "<=" (.var "L_xp") (.bin "+" (.var "R_xp") (.num "0.0"))) (.cmp "<=" (.var "R_xp") (.bin "+" (.var "L_xp") (.num "0.0")))) (.cmp ">=" (.var "L_xp") (.num "25.0"))) (.cmp ">=" (.var "R_xp") (.num "25.0"))))]
    stutter := true }

end RelCertifier.Parse
