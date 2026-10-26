/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hvac_fan_staging` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py hvac_fan_staging`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/hvac_fan_staging/input.txt` (do not edit). -/
def hvac_fan_staging_IRv2 : PProblem :=
  {
    name := "hvac_fan_staging"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["T"]
      epsilon := "1.0"
      modes := [
        {
          name := "LOW"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "27.0") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<" (.var "T") (.num "23.5")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "MED"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "24.0") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "23.5")) (.cmp "<=" (.var "T") (.num "24.5")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "HIGH"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "21.0") (.var "T"))))]
          guard := (.and (.cmp ">" (.var "T") (.num "24.5")) (.cmp "<=" (.var "T") (.num "32.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] } ] }
    R := {
      stateVars := ["T"]
      epsilon := "1.0"
      modes := [
        {
          name := "LOW"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "27.0") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "25.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "MED"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "24.0") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "HIGH"
          odes := [("T", (.bin "*" (.num "0.05") (.bin "-" (.num "21.0") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "23.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "16.0")) (.cmp "<=" (.var "T") (.num "32.0")))
          next := ["LOW", "MED", "HIGH"] } ] }
    invariants := [
      ("LOW", (.and (.cmp "<=" (.var "L_T") (.var "R_T")) (.cmp "<=" (.var "R_T") (.var "L_T")))),
      ("MED", (.and (.cmp "<=" (.var "L_T") (.var "R_T")) (.cmp "<=" (.var "R_T") (.var "L_T")))),
      ("HIGH", (.and (.cmp "<=" (.var "L_T") (.var "R_T")) (.cmp "<=" (.var "R_T") (.var "L_T"))))] }

end RelCertifier.Parse
