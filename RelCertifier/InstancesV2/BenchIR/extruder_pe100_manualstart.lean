/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `extruder_pe100_manualstart` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py extruder_pe100_manualstart`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/extruder_pe100_manualstart/input.txt` (do not edit). -/
def extruder_pe100_manualstart_IRv2 : PProblem :=
  {
    name := "extruder_pe100_manualstart"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["T", "p"]
      epsilon := "2.0"
      modes := [
        {
          name := "N1"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "1.33")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "186")) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N2"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "3.39")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "186")) (.cmp "<=" (.var "T") (.num "206"))) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N3"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "8.64")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "206")) (.cmp "<=" (.var "T") (.num "226"))) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N4"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "22.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "226")) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] } ] }
    R := {
      stateVars := ["T", "p"]
      epsilon := "1.0"
      modes := [
        {
          name := "N1"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "1.33")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "186")) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N2"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "3.39")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "186")) (.cmp "<=" (.var "T") (.num "206"))) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N3"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "8.64")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "206")) (.cmp "<=" (.var "T") (.num "226"))) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] },
        {
          name := "N4"
          odes := [("T", (.bin "*" (.num "0.5") (.bin "-" (.bin "+" (.var "p") (.num "22.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "226")) (.cmp ">=" (.var "T") (.num "130"))) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300"))) (.cmp ">=" (.var "p") (.num "180"))) (.cmp "<=" (.var "p") (.num "220")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "130")) (.cmp "<=" (.var "T") (.num "300"))) (.cmp ">=" (.var "p") (.num "0"))) (.cmp "<=" (.var "p") (.num "300")))
          next := ["N1", "N2", "N3", "N4"] } ] }
    invariants := [
      ("N1", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "18.61"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "18.61")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("N2", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "18.61"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "18.61")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("N3", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "18.61"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "18.61")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("N4", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "18.61"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "18.61")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p"))))] }

end RelCertifier.Parse
