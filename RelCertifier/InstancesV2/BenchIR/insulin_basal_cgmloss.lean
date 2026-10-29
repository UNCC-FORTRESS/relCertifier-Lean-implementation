/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `insulin_basal_cgmloss` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py insulin_basal_cgmloss`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/insulin_basal_cgmloss/input.txt` (do not edit). -/
def insulin_basal_cgmloss_IRv2 : PProblem :=
  {
    name := "insulin_basal_cgmloss"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["X", "G", "b"]
      epsilon := "10.0"
      modes := [
        {
          name := "SUSP"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.0") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "G") (.num "70")) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["SUSP", "L1", "L2"] },
        {
          name := "L1"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.2") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "70")) (.cmp "<" (.var "G") (.num "100"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["SUSP", "L1", "L2", "L3"] },
        {
          name := "L2"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.4") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "100")) (.cmp "<" (.var "G") (.num "130"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["SUSP", "L1", "L2", "L3", "L4"] },
        {
          name := "L3"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.6") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "130")) (.cmp "<" (.var "G") (.num "160"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L1", "L2", "L3", "L4", "L5"] },
        {
          name := "L4"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.8") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "160")) (.cmp "<" (.var "G") (.num "190"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L2", "L3", "L4", "L5", "L6"] },
        {
          name := "L5"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.0") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "190")) (.cmp "<" (.var "G") (.num "220"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L3", "L4", "L5", "L6", "L7"] },
        {
          name := "L6"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.2") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "220")) (.cmp "<" (.var "G") (.num "250"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L4", "L5", "L6", "L7", "L8"] },
        {
          name := "L7"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.4") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "250")) (.cmp "<" (.var "G") (.num "280"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L5", "L6", "L7", "L8"] },
        {
          name := "L8"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.6") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "280")) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L6", "L7", "L8"] } ] }
    R := {
      stateVars := ["X", "G", "b"]
      epsilon := "5.0"
      modes := [
        {
          name := "SUSP"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.0") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "G") (.num "70")) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["SUSP", "L1"] },
        {
          name := "L1"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.2") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "70")) (.cmp "<" (.var "G") (.num "100"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["SUSP", "L1", "L2"] },
        {
          name := "L2"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.4") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "100")) (.cmp "<" (.var "G") (.num "130"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L1", "L2", "L3"] },
        {
          name := "L3"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.6") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "130")) (.cmp "<" (.var "G") (.num "160"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L2", "L3", "L4"] },
        {
          name := "L4"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "0.8") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "160")) (.cmp "<" (.var "G") (.num "190"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L3", "L4", "L5"] },
        {
          name := "L5"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.0") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "190")) (.cmp "<" (.var "G") (.num "220"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L4", "L5", "L6"] },
        {
          name := "L6"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.2") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "220")) (.cmp "<" (.var "G") (.num "250"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L5", "L6", "L7"] },
        {
          name := "L7"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.4") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "250")) (.cmp "<" (.var "G") (.num "280"))) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L6", "L7", "L8"] },
        {
          name := "L8"
          odes := [("X", (.bin "*" (.num "0.018182") (.bin "-" (.num "1.6") (.var "X")))),
            ("G", (.bin "*" (.num "0.016667") (.bin "-" (.bin "+" (.num "120.0") (.bin "*" (.num "50.0") (.bin "-" (.var "b") (.var "X")))) (.var "G")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "G") (.num "280")) (.cmp ">=" (.var "X") (.num "0.0"))) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "X") (.num "0.0")) (.cmp "<=" (.var "X") (.num "1.6"))) (.cmp ">=" (.var "G") (.num "40.0"))) (.cmp "<=" (.var "G") (.num "400.0"))) (.cmp ">=" (.var "b") (.num "0.5"))) (.cmp "<=" (.var "b") (.num "1.3")))
          next := ["L7", "L8"] } ] }
    invariants := [
      ("SUSP", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L1", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L2", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L3", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L4", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L5", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L6", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L7", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("L8", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_X") (.bin "+" (.var "R_X") (.num "0.5"))) (.cmp "<=" (.var "R_X") (.bin "+" (.var "L_X") (.num "0.5")))) (.cmp "<=" (.var "L_G") (.bin "+" (.var "R_G") (.num "25")))) (.cmp "<=" (.var "R_G") (.bin "+" (.var "L_G") (.num "25")))) (.cmp "<=" (.var "L_b") (.var "R_b"))) (.cmp "<=" (.var "R_b") (.var "L_b"))))] }

end RelCertifier.Parse
