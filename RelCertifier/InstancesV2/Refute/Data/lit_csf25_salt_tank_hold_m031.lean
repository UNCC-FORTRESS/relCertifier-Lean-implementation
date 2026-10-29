/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold_m031`: a mutant of `lit_csf25_salt_tank_hold` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(>= (+ R_xp (* L_t 0.1)) 35.5) [R_xp->L_xp]` of `benchmarks/suite_v2/lit_csf25_salt_tank_hold`; file `benchmarks/refute_mutants/lit_csf25_salt_tank_hold_m031/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/lit_csf25_salt_tank_hold_m031/input.txt` (do not edit). -/
def lit_csf25_salt_tank_hold_m031_IRm : PProblem :=
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
          guard := (.and (.and (.and (.cmp ">" (.var "xp") (.num "36.43")) (.cmp "<" (.var "xp") (.num "36.93"))) (.cmp ">=" (.var "t") (.num "5.0"))) (.cmp "<=" (.var "t") (.num "5.0")))
          evolve := (.and (.cmp ">=" (.var "xp") (.num "0.0")) (.cmp "<=" (.var "xp") (.num "300.0")))
          next := ["HoldInc"] },
        {
          name := "HoldDec"
          odes := [("xp", (.bin "*" (.num "0.03") (.bin "-" (.num "25.0") (.var "xp")))),
            ("t", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "xp") (.num "34.7")) (.cmp "<" (.var "xp") (.num "36.75"))) (.cmp ">=" (.var "t") (.num "5.0"))) (.cmp "<=" (.var "t") (.num "5.0")))
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
      ("HoldInc", (.and (.and (.and (.cmp "<=" (.var "R_xp") (.var "L_xp")) (.cmp "<=" (.var "L_xp") (.bin "-" (.bin "+" (.var "R_xp") (.bin "*" (.var "L_t") (.num "1.25"))) (.num "4.15")))) (.cmp ">=" (.var "R_xp") (.num "34.5"))) (.cmp "<=" (.var "R_xp") (.bin "+" (.bin "*" (.var "L_t") (.num "0.655")) (.num "31.724"))))),
      ("HoldDec", (.and (.and (.and (.cmp "<=" (.var "L_xp") (.var "R_xp")) (.cmp "<=" (.var "R_xp") (.bin "-" (.bin "+" (.var "L_xp") (.bin "*" (.var "L_t") (.num "0.23"))) (.num "0.65")))) (.cmp "<=" (.var "R_xp") (.num "37.1"))) (.cmp ">=" (.bin "+" (.var "L_xp") (.bin "*" (.var "L_t") (.num "0.1"))) (.num "35.5"))))] }

/-- The finder's witness (kind B). -/
def lit_csf25_salt_tank_hold_m031_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 1, k := 3,
    wL := [(35 : ℚ), (5 : ℚ), (0 : ℚ)],
    wR := [(35 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
