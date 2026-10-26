/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `airheader_dos_3to1` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py airheader_dos_3to1`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/airheader_dos_3to1/input.txt` (do not edit). -/
def airheader_dos_3to1_IRv2 : PProblem :=
  {
    name := "airheader_dos_3to1"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "g"]
      epsilon := "3.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("p", (.bin "-" (.bin "*" (.num "0.1") (.bin "-" (.num "9.0") (.var "p"))) (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "p") (.num "6.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["NORMAL", "ALARM", "TRIP"] },
        {
          name := "ALARM"
          odes := [("p", (.bin "-" (.bin "*" (.num "0.1") (.bin "-" (.num "9.0") (.var "p"))) (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "p") (.num "5.0")) (.cmp "<" (.var "p") (.num "6.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["NORMAL", "ALARM", "TRIP"] },
        {
          name := "TRIP"
          odes := [("p", (.bin "-" (.num "0.0") (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp "<" (.var "p") (.num "5.0")) (.cmp ">=" (.var "p") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["TRIP"] } ] }
    R := {
      stateVars := ["p", "g"]
      epsilon := "1.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("p", (.bin "-" (.bin "*" (.num "0.1") (.bin "-" (.num "9.0") (.var "p"))) (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "p") (.num "6.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["NORMAL", "ALARM", "TRIP"] },
        {
          name := "ALARM"
          odes := [("p", (.bin "-" (.bin "*" (.num "0.1") (.bin "-" (.num "9.0") (.var "p"))) (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "p") (.num "5.0")) (.cmp "<" (.var "p") (.num "6.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["NORMAL", "ALARM", "TRIP"] },
        {
          name := "TRIP"
          odes := [("p", (.bin "-" (.num "0.0") (.bin "*" (.var "g") (.var "p")))),
            ("g", (.num "0.0"))]
          guard := (.and (.and (.and (.cmp "<" (.var "p") (.num "5.0")) (.cmp ">=" (.var "p") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "9.0"))) (.cmp ">=" (.var "g") (.num "0.02"))) (.cmp "<=" (.var "g") (.num "0.06")))
          next := ["TRIP"] } ] }
    invariants := [
      ("NORMAL", (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_g") (.var "R_g"))) (.cmp "<=" (.var "R_g") (.var "L_g")))),
      ("ALARM", (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_g") (.var "R_g"))) (.cmp "<=" (.var "R_g") (.var "L_g")))),
      ("TRIP", (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_g") (.var "R_g"))) (.cmp "<=" (.var "R_g") (.var "L_g"))))] }

end RelCertifier.Parse
