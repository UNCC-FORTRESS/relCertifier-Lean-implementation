/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `furnace_program_timebase` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py furnace_program_timebase`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/furnace_program_timebase/input.txt` (do not edit). -/
def furnace_program_timebase_IRv2 : PProblem :=
  {
    name := "furnace_program_timebase"
    lambdaMin := "0.8"
    lambdaMax := "1.0"
    L := {
      stateVars := ["s", "T"]
      epsilon := "1.0"
      modes := [
        {
          name := "PREHEAT"
          odes := [("s", (.bin "*" (.num "0.008") (.bin "-" (.num "650.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "s") (.num "640.0")) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["PREHEAT", "HEAT"] },
        {
          name := "HEAT"
          odes := [("s", (.bin "*" (.num "0.008") (.bin "-" (.num "870.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "640.0")) (.cmp "<" (.var "s") (.num "860.0"))) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["HEAT", "SOAK"] },
        {
          name := "SOAK"
          odes := [("s", (.bin "*" (.num "0.08") (.bin "-" (.num "870.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "860.0")) (.cmp "<=" (.var "s") (.num "870.0"))) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["SOAK"] } ] }
    R := {
      stateVars := ["s", "T"]
      epsilon := "1.0"
      modes := [
        {
          name := "PREHEAT"
          odes := [("s", (.bin "*" (.num "0.01") (.bin "-" (.num "650.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "s") (.num "640.0")) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["PREHEAT", "HEAT"] },
        {
          name := "HEAT"
          odes := [("s", (.bin "*" (.num "0.01") (.bin "-" (.num "870.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "640.0")) (.cmp "<" (.var "s") (.num "860.0"))) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["HEAT", "SOAK"] },
        {
          name := "SOAK"
          odes := [("s", (.bin "*" (.num "0.1") (.bin "-" (.num "870.0") (.var "s")))),
            ("T", (.bin "*" (.num "0.2") (.bin "-" (.var "s") (.var "T"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "860.0")) (.cmp "<=" (.var "s") (.num "870.0"))) (.cmp ">=" (.var "s") (.num "20.0"))) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "s") (.num "20.0")) (.cmp "<=" (.var "s") (.num "900.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "900.0")))
          next := ["SOAK"] } ] }
    invariants := [
      ("PREHEAT", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0")))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.bin "-" (.var "R_s") (.var "R_T")) (.num "32.0"))) (.cmp "<=" (.var "R_T") (.var "R_s")))),
      ("HEAT", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0")))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.bin "-" (.var "R_s") (.var "R_T")) (.num "32.0"))) (.cmp "<=" (.var "R_T") (.var "R_s")))),
      ("SOAK", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "8.0")))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "8.0")))) (.cmp "<=" (.bin "-" (.var "R_s") (.var "R_T")) (.num "32.0"))) (.cmp "<=" (.var "R_T") (.var "R_s"))))] }

end RelCertifier.Parse
