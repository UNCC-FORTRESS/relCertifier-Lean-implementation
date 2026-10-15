/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_car_stop` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py drl_car_stop`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/drl_car_stop/input.txt` (do not edit). -/
def drl_car_stop_IRv2 : PProblem :=
  {
    name := "drl_car_stop"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["x", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accel"
          odes := [("x", (.var "v")),
            ("v", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "9.0"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "+" (.var "x") (.bin "*" (.bin "*" (.num "0.5") (.var "v")) (.var "v"))) (.bin "*" (.num "2.0") (.var "v"))) (.num "1.0")) (.num "50.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Coast"
          odes := [("x", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Brake"
          odes := [("x", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] } ] }
    R := {
      stateVars := ["x", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accel"
          odes := [("x", (.var "v")),
            ("v", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "9.0"))) (.cmp "<=" (.bin "+" (.var "x") (.bin "*" (.bin "*" (.num "0.5") (.var "v")) (.var "v"))) (.num "50.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Coast"
          odes := [("x", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] },
        {
          name := "Brake"
          odes := [("x", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "10.0")))
          next := ["Accel", "Coast", "Brake"] } ] }
    invariants := [
      ("Accel", (.and (.and (.and (.cmp "<=" (.var "L_x") (.var "R_x")) (.cmp "<=" (.var "R_x") (.var "L_x"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("Coast", (.and (.and (.and (.cmp "<=" (.var "L_x") (.var "R_x")) (.cmp "<=" (.var "R_x") (.var "L_x"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("Brake", (.and (.and (.and (.cmp "<=" (.var "L_x") (.var "R_x")) (.cmp "<=" (.var "R_x") (.var "L_x"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))))] }

end RelCertifier.Parse
