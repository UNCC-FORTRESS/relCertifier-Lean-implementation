/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bms_chiller_undercharge` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bms_chiller_undercharge`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/bms_chiller_undercharge/input.txt` (do not edit). -/
def bms_chiller_undercharge_IRv2 : PProblem :=
  {
    name := "bms_chiller_undercharge"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["T"]
      epsilon := "1.0"
      modes := [
        {
          name := "COAST"
          odes := [("T", (.bin "*" (.num "0.02") (.bin "-" (.num "50") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<" (.var "T") (.num "28.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          next := ["COAST", "CHILL"] },
        {
          name := "CHILL"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "27") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "28.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          next := ["COAST", "CHILL"] } ] }
    R := {
      stateVars := ["T"]
      epsilon := "1.0"
      modes := [
        {
          name := "COAST"
          odes := [("T", (.bin "*" (.num "0.02") (.bin "-" (.num "50") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          next := ["COAST", "CHILL_LO", "CHILL_HI"] },
        {
          name := "CHILL_LO"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "30") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "20.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          next := ["COAST", "CHILL_LO", "CHILL_HI"] },
        {
          name := "CHILL_HI"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "20") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "20.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "60.0")))
          next := ["COAST", "CHILL_LO", "CHILL_HI"] } ] }
    invariants := [
      ("COAST", (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "5.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "5.0"))))),
      ("CHILL", (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "5.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "5.0")))))] }

end RelCertifier.Parse
