/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` (choice exhibit) — parser-emitted IR literal (GENERATED leaf — do not edit)
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/choice/vehicle_hypercert/input.txt` (do not edit). -/
def vehicle_hypercert_IRc : PProblem :=
  {
    name := "vehicle_hypercert"
    lambdaMin := "1.0"
    lambdaMax := "2.0"
    L := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Am4"
          odes := [("v", (.bin "-" (.num "0.0") (.num "0.04")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.04")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Am2"
          odes := [("v", (.bin "-" (.num "0.0") (.num "0.02")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.02")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "A0"
          odes := [("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap2"
          odes := [("v", (.num "0.02"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.58")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap4"
          odes := [("v", (.num "0.04"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.56")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Am4"
          odes := [("v", (.bin "-" (.num "0.0") (.num "0.04")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.04")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Am2"
          odes := [("v", (.bin "-" (.num "0.0") (.num "0.02")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.02")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "A0"
          odes := [("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap2"
          odes := [("v", (.num "0.02"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.58")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap4"
          odes := [("v", (.num "0.04"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.56")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] } ] }
    invariants := [
      ("Am4", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("Am2", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("A0", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("Ap2", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("Ap4", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))))] }

end RelCertifier.Parse
