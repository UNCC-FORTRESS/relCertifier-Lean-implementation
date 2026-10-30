/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `fuelcell_chp_dos` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py fuelcell_chp_dos`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/fuelcell_chp_dos/input.txt` (do not edit). -/
def fuelcell_chp_dos_IRv2 : PProblem :=
  {
    name := "fuelcell_chp_dos"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["T", "Tin"]
      epsilon := "20.0"
      modes := [
        {
          name := "LOW"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "12")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "52.0")) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "MED"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "17")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "52.0")) (.cmp "<=" (.var "T") (.num "78.0"))) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "HIGH"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "22")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "78.0")) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] } ] }
    R := {
      stateVars := ["T", "Tin"]
      epsilon := "10.0"
      modes := [
        {
          name := "LOW"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "12")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "60.0")) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "MED"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "17")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "50.0")) (.cmp "<" (.var "T") (.num "80.0"))) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] },
        {
          name := "HIGH"
          odes := [("T", (.bin "*" (.num "0.00833333") (.bin "-" (.bin "+" (.var "Tin") (.num "22")) (.var "T")))),
            ("Tin", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "70.0")) (.cmp ">=" (.var "Tin") (.num "40"))) (.cmp "<=" (.var "Tin") (.num "56"))) (.cmp ">=" (.var "T") (.num "0.0"))) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "0.0")) (.cmp "<=" (.var "T") (.num "100.0"))) (.cmp ">=" (.var "Tin") (.num "0"))) (.cmp "<=" (.var "Tin") (.num "100")))
          next := ["LOW", "MED", "HIGH"] } ] }
    invariants := [
      ("LOW", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "7.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "7.0")))) (.cmp "<=" (.var "L_Tin") (.var "R_Tin"))) (.cmp "<=" (.var "R_Tin") (.var "L_Tin")))),
      ("MED", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "7.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "7.0")))) (.cmp "<=" (.var "L_Tin") (.var "R_Tin"))) (.cmp "<=" (.var "R_Tin") (.var "L_Tin")))),
      ("HIGH", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "7.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "7.0")))) (.cmp "<=" (.var "L_Tin") (.var "R_Tin"))) (.cmp "<=" (.var "R_Tin") (.var "L_Tin"))))] }

end RelCertifier.Parse
