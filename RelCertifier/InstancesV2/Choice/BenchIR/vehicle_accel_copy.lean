/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice exhibit) — parser-emitted IR literal (GENERATED leaf — do not edit)
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/choice/vehicle_accel_copy/input.txt` (do not edit). -/
def vehicle_accel_copy_IRc : PProblem :=
  {
    name := "vehicle_accel_copy"
    lambdaMin := "1.0"
    lambdaMax := "2.0"
    L := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accel"
          odes := [("v", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "25.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Coast"
          odes := [("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Brake"
          odes := [("v", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "5.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accel"
          odes := [("v", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "27.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Coast"
          odes := [("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Brake"
          odes := [("v", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "3.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          next := ["Accel", "Coast", "Brake"] } ] }
    invariants := [
      ("Accel", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "1"))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "1"))))),
      ("Coast", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "1"))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "1"))))),
      ("Brake", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "1"))) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "1")))))] }

end RelCertifier.Parse
