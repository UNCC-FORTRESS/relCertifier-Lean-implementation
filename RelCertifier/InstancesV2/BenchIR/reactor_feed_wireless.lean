/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `reactor_feed_wireless` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py reactor_feed_wireless`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/reactor_feed_wireless/input.txt` (do not edit). -/
def reactor_feed_wireless_IRv2 : PProblem :=
  {
    name := "reactor_feed_wireless"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["T", "p"]
      epsilon := "2.0"
      modes := [
        {
          name := "F1"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "4.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "25.0")) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F2"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "8.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "25.0")) (.cmp "<" (.var "T") (.num "35.0"))) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F3"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "12.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "35.0")) (.cmp "<=" (.var "T") (.num "45.0"))) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F4"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "16.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "45.0")) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] } ] }
    R := {
      stateVars := ["T", "p"]
      epsilon := "1.0"
      modes := [
        {
          name := "F1"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "4.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "T") (.num "25.0")) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F2"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "8.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "25.0")) (.cmp "<" (.var "T") (.num "35.0"))) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F3"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "12.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "T") (.num "35.0")) (.cmp "<=" (.var "T") (.num "45.0"))) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] },
        {
          name := "F4"
          odes := [("T", (.bin "*" (.num "0.1") (.bin "-" (.bin "+" (.var "p") (.num "16.0")) (.var "T")))),
            ("p", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.cmp ">" (.var "T") (.num "45.0")) (.cmp ">=" (.var "T") (.num "15.0"))) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "T") (.num "15.0")) (.cmp "<=" (.var "T") (.num "60.0"))) (.cmp ">=" (.var "p") (.num "15.0"))) (.cmp "<=" (.var "p") (.num "35.0")))
          next := ["F1", "F2", "F3", "F4"] } ] }
    invariants := [
      ("F1", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("F2", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("F3", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p")))),
      ("F4", (.and (.and (.and (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0"))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.var "L_p") (.var "R_p"))) (.cmp "<=" (.var "R_p") (.var "L_p"))))] }

end RelCertifier.Parse
