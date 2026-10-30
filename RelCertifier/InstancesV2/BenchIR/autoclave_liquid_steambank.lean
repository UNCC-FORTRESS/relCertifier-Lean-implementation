/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `autoclave_liquid_steambank` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py autoclave_liquid_steambank`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/autoclave_liquid_steambank/input.txt` (do not edit). -/
def autoclave_liquid_steambank_IRv2 : PProblem :=
  {
    name := "autoclave_liquid_steambank"
    lambdaMin := "0.75"
    lambdaMax := "1.0"
    L := {
      stateVars := ["c", "T", "t"]
      epsilon := "0.1"
      modes := [
        {
          name := "HEAT"
          odes := [("c", (.num "3.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "c") (.num "122.0")) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["HEAT", "EQUIL", "EXPOSE"] },
        {
          name := "EQUIL"
          odes := [("c", (.num "0.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "122.0")) (.cmp "<=" (.var "c") (.num "124.0"))) (.cmp "<" (.var "T") (.num "121.0"))) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EQUIL", "EXPOSE"] },
        {
          name := "EXPOSE"
          odes := [("c", (.num "0.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "1.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "122.0")) (.cmp "<=" (.var "c") (.num "124.0"))) (.cmp ">=" (.var "T") (.num "121.0"))) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EXPOSE", "EXHAUST"] },
        {
          name := "EXHAUST"
          odes := [("c", (.bin "*" (.num "0.1") (.bin "-" (.num "100.0") (.var "c")))),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "15.0")) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EXHAUST"] } ] }
    R := {
      stateVars := ["c", "T", "t"]
      epsilon := "0.1"
      modes := [
        {
          name := "HEAT"
          odes := [("c", (.num "4.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "c") (.num "122.0")) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["HEAT", "EQUIL", "EXPOSE"] },
        {
          name := "EQUIL"
          odes := [("c", (.num "0.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "122.0")) (.cmp "<=" (.var "c") (.num "124.0"))) (.cmp "<" (.var "T") (.num "121.0"))) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EQUIL", "EXPOSE"] },
        {
          name := "EXPOSE"
          odes := [("c", (.num "0.0")),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "1.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "122.0")) (.cmp "<=" (.var "c") (.num "124.0"))) (.cmp ">=" (.var "T") (.num "121.0"))) (.cmp "<" (.var "t") (.num "15.0"))) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EXPOSE", "EXHAUST"] },
        {
          name := "EXHAUST"
          odes := [("c", (.bin "*" (.num "0.1") (.bin "-" (.num "100.0") (.var "c")))),
            ("T", (.bin "*" (.num "0.1") (.bin "-" (.var "c") (.var "T")))),
            ("t", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "15.0")) (.cmp ">=" (.var "c") (.num "20.0"))) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "c") (.num "20.0")) (.cmp "<=" (.var "c") (.num "138.0"))) (.cmp ">=" (.var "T") (.num "20.0"))) (.cmp "<=" (.var "T") (.num "138.0"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["EXHAUST"] } ] }
    invariants := [
      ("HEAT", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_c") (.var "R_c")) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "10.0")))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "0.0")))) (.cmp "<=" (.bin "-" (.var "R_c") (.var "R_T")) (.num "40.0"))) (.cmp "<=" (.var "R_T") (.var "R_c")))),
      ("EQUIL", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_c") (.var "R_c")) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_T") (.bin "+" (.var "R_T") (.num "10.0")))) (.cmp "<=" (.var "R_T") (.bin "+" (.var "L_T") (.num "0.0")))) (.cmp "<=" (.bin "-" (.var "R_c") (.var "R_T")) (.num "40.0"))) (.cmp "<=" (.var "R_T") (.var "R_c")))),
      ("EXPOSE", (.and (.and (.and (.cmp "<=" (.var "L_c") (.var "R_c")) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t")))),
      ("EXHAUST", (.and (.and (.and (.cmp "<=" (.var "L_c") (.var "R_c")) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t"))))] }

end RelCertifier.Parse
