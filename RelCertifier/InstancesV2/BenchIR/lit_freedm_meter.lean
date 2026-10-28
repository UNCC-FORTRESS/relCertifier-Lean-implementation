/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_freedm_meter` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_freedm_meter`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/lit_freedm_meter/input.txt` (do not edit). -/
def lit_freedm_meter_IRv2 : PProblem :=
  {
    name := "lit_freedm_meter"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["B", "E"]
      epsilon := "1.0"
      modes := [
        {
          name := "BatD0R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD0R1"
          odes := [("B", (.num "1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "9.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD1R0"
          odes := [("B", (.num "-1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "1.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD1R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD2R0"
          odes := [("B", (.num "-2.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "2.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD2R1"
          odes := [("B", (.num "-1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "1.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD0R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD0R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "-1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD1R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD1R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD2R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "2.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD2R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] } ] }
    R := {
      stateVars := ["B", "E"]
      epsilon := "1.0"
      modes := [
        {
          name := "BatD0R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD0R1"
          odes := [("B", (.num "1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "9.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD1R0"
          odes := [("B", (.num "-1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "1.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD1R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD2R0"
          odes := [("B", (.num "-2.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "2.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "BatD2R1"
          odes := [("B", (.num "-1.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "1.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD0R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD0R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "-1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD1R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD1R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD2R0"
          odes := [("B", (.num "0.0")),
            ("E", (.num "2.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] },
        {
          name := "GridD2R1"
          odes := [("B", (.num "0.0")),
            ("E", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "B") (.num "0.0")) (.cmp "<=" (.var "B") (.num "10.0")))
          next := ["BatD0R0", "BatD0R1", "BatD1R0", "BatD1R1", "BatD2R0", "BatD2R1", "GridD0R0", "GridD0R1", "GridD1R0", "GridD1R1", "GridD2R0", "GridD2R1"] } ] }
    invariants := [
      ("BatD0R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("BatD0R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("BatD1R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("BatD1R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("BatD2R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("BatD2R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD0R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD0R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD1R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD1R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD2R0", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E")))),
      ("GridD2R1", (.and (.cmp "<=" (.var "L_E") (.var "R_E")) (.cmp "<=" (.var "R_E") (.var "L_E"))))] }

end RelCertifier.Parse
