/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `compressor_station_recycle` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py compressor_station_recycle`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/compressor_station_recycle/input.txt` (do not edit). -/
def compressor_station_recycle_IRv2 : PProblem :=
  {
    name := "compressor_station_recycle"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["ps", "pd"]
      epsilon := "1.0"
      modes := [
        {
          name := "HIGH"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.4000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "0.9000")))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "pd") (.num "61.0")) (.cmp ">=" (.var "ps") (.num "45.0"))) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["HIGH", "MED", "LOW"] },
        {
          name := "MED"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.4000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "0.9000")))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "pd") (.num "61.0")) (.cmp "<=" (.var "pd") (.num "64.0"))) (.cmp ">=" (.var "ps") (.num "45.0"))) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["HIGH", "MED", "LOW"] },
        {
          name := "LOW"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.2000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "0.4500")))]
          guard := (.and (.and (.and (.and (.cmp ">" (.var "pd") (.num "64.0")) (.cmp ">=" (.var "ps") (.num "45.0"))) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["HIGH", "MED", "LOW"] } ] }
    R := {
      stateVars := ["ps", "pd"]
      epsilon := "1.0"
      modes := [
        {
          name := "LOW"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.2000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "0.4500")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "pd") (.num "60.0")) (.cmp ">=" (.var "ps") (.num "45.0"))) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "MED"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.4000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "0.9000")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "HIGH"
          odes := [("ps", (.bin "-" (.bin "*" (.num "0.05") (.bin "-" (.num "62.0") (.var "ps"))) (.num "0.6000"))),
            ("pd", (.bin "+" (.bin "*" (.num "0.05") (.bin "-" (.num "40.0") (.var "pd"))) (.num "1.3500")))]
          guard := (.and (.and (.and (.and (.cmp "<=" (.var "pd") (.num "66.0")) (.cmp ">=" (.var "ps") (.num "45.0"))) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "ps") (.num "45.0")) (.cmp "<=" (.var "ps") (.num "62.0"))) (.cmp ">=" (.var "pd") (.num "40.0"))) (.cmp "<=" (.var "pd") (.num "70.0")))
          next := ["LOW", "MED", "HIGH"] } ] }
    invariants := [
      ("HIGH", (.and (.and (.and (.cmp "<=" (.var "L_ps") (.bin "+" (.var "R_ps") (.num "0"))) (.cmp "<=" (.var "R_ps") (.bin "+" (.var "L_ps") (.num "0")))) (.cmp "<=" (.var "L_pd") (.bin "+" (.var "R_pd") (.num "0")))) (.cmp "<=" (.var "R_pd") (.bin "+" (.var "L_pd") (.num "0"))))),
      ("MED", (.and (.and (.and (.cmp "<=" (.var "L_ps") (.bin "+" (.var "R_ps") (.num "0"))) (.cmp "<=" (.var "R_ps") (.bin "+" (.var "L_ps") (.num "0")))) (.cmp "<=" (.var "L_pd") (.bin "+" (.var "R_pd") (.num "0")))) (.cmp "<=" (.var "R_pd") (.bin "+" (.var "L_pd") (.num "0"))))),
      ("LOW", (.and (.and (.and (.cmp "<=" (.var "L_ps") (.bin "+" (.var "R_ps") (.num "0"))) (.cmp "<=" (.var "R_ps") (.bin "+" (.var "L_ps") (.num "0")))) (.cmp "<=" (.var "L_pd") (.bin "+" (.var "R_pd") (.num "0")))) (.cmp "<=" (.var "R_pd") (.bin "+" (.var "L_pd") (.num "0")))))] }

end RelCertifier.Parse
