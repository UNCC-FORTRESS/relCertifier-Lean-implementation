/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `zone_lightmass_schedule` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py zone_lightmass_schedule`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/zone_lightmass_schedule/input.txt` (do not edit). -/
def zone_lightmass_schedule_IRv2 : PProblem :=
  {
    name := "zone_lightmass_schedule"
    lambdaMin := "2.0"
    lambdaMax := "2.0"
    L := {
      stateVars := ["T"]
      epsilon := "5.0"
      modes := [
        {
          name := "COMFORT"
          odes := [("T", (.bin "*" (.num "0.04125") (.bin "-" (.num "21") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          next := ["COMFORT", "ECONOMY"] },
        {
          name := "ECONOMY"
          odes := [("T", (.bin "*" (.num "0.04125") (.bin "-" (.num "16") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          next := ["ECONOMY", "COMFORT"] } ] }
    R := {
      stateVars := ["T"]
      epsilon := "5.0"
      modes := [
        {
          name := "COMFORT"
          odes := [("T", (.bin "*" (.num "0.02") (.bin "-" (.num "21") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          next := ["COMFORT", "STANDBY", "ECONOMY"] },
        {
          name := "STANDBY"
          odes := [("T", (.bin "*" (.num "0.02") (.bin "-" (.num "19") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          next := ["STANDBY", "COMFORT", "ECONOMY"] },
        {
          name := "ECONOMY"
          odes := [("T", (.bin "*" (.num "0.02") (.bin "-" (.num "16") (.var "T"))))]
          guard := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "T") (.num "5.0")) (.cmp "<=" (.var "T") (.num "30.0")))
          next := ["ECONOMY", "COMFORT", "STANDBY"] } ] }
    invariants := [
      ("COMFORT", (.and (.cmp "<=" (.bin "-" (.var "L_T") (.var "R_T")) (.num "0.5")) (.cmp "<=" (.bin "-" (.var "R_T") (.var "L_T")) (.num "0.5")))),
      ("ECONOMY", (.and (.cmp "<=" (.bin "-" (.var "L_T") (.var "R_T")) (.num "0.5")) (.cmp "<=" (.bin "-" (.var "R_T") (.var "L_T")) (.num "0.5"))))] }

end RelCertifier.Parse
