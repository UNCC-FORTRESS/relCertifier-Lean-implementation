/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `train_ato_odometry` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py train_ato_odometry`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/train_ato_odometry/input.txt` (do not edit). -/
def train_ato_odometry_IRv2 : PProblem :=
  {
    name := "train_ato_odometry"
    lambdaMin := "0.75"
    lambdaMax := "1.25"
    L := {
      stateVars := ["v"]
      epsilon := "0.5"
      modes := [
        {
          name := "PL1"
          odes := [("v", (.bin "*" (.num "0.05") (.bin "-" (.num "25.0") (.bin "*" (.num "0.96") (.var "v")))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          next := ["PL1", "PL2", "PL3"] },
        {
          name := "PL2"
          odes := [("v", (.bin "*" (.num "0.045") (.bin "-" (.num "25.0") (.bin "*" (.num "0.96") (.var "v")))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          next := ["PL1", "PL2", "PL3"] },
        {
          name := "PL3"
          odes := [("v", (.bin "*" (.num "0.04") (.bin "-" (.num "25.0") (.bin "*" (.num "0.96") (.var "v")))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "28.21")))
          next := ["PL1", "PL2", "PL3"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "0.5"
      modes := [
        {
          name := "PL1"
          odes := [("v", (.bin "*" (.num "0.05") (.bin "-" (.num "25.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          next := ["PL1", "PL2", "PL3"] },
        {
          name := "PL2"
          odes := [("v", (.bin "*" (.num "0.045") (.bin "-" (.num "25.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          next := ["PL1", "PL2", "PL3"] },
        {
          name := "PL3"
          odes := [("v", (.bin "*" (.num "0.04") (.bin "-" (.num "25.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "27.08")))
          next := ["PL1", "PL2", "PL3"] } ] }
    invariants := [
      ("PL1", (.and (.cmp "<=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "1.11")) (.cmp ">=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "0.0")))),
      ("PL2", (.and (.cmp "<=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "1.11")) (.cmp ">=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "0.0")))),
      ("PL3", (.and (.cmp "<=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "1.11")) (.cmp ">=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "0.0"))))] }

end RelCertifier.Parse
