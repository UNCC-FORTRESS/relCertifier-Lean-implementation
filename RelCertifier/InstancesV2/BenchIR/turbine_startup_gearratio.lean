/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py turbine_startup_gearratio`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/turbine_startup_gearratio/input.txt` (do not edit). -/
def turbine_startup_gearratio_IRv2 : PProblem :=
  {
    name := "turbine_startup_gearratio"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["w"]
      epsilon := "1.0"
      modes := [
        {
          name := "SPINUP"
          odes := [("w", (.bin "*" (.num "0.03") (.bin "-" (.num "9") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "2.1")) (.cmp "<" (.var "w") (.num "5.25")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755")))
          next := ["SPINUP", "RAMP", "STOP"] },
        {
          name := "RAMP"
          odes := [("w", (.bin "*" (.num "0.0380952") (.bin "-" (.num "7.875") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "5.25")) (.cmp "<" (.var "w") (.num "7.245")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755")))
          next := ["RAMP", "GEN", "STOP"] },
        {
          name := "GEN"
          odes := [("w", (.bin "*" (.num "0.047619") (.bin "-" (.num "12.705") (.var "w"))))]
          guard := (.cmp ">=" (.var "w") (.num "7.245"))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755")))
          next := ["GEN"] },
        {
          name := "STOP"
          odes := [("w", (.bin "*" (.neg (.num "0.1")) (.var "w")))]
          guard := (.cmp "<" (.var "w") (.num "2.1"))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["w"]
      epsilon := "1.0"
      modes := [
        {
          name := "SPINUP"
          odes := [("w", (.bin "*" (.num "0.03") (.bin "-" (.num "9") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "2.0")) (.cmp "<" (.var "w") (.num "5.0")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31")))
          next := ["SPINUP", "RAMP", "STOP"] },
        {
          name := "RAMP"
          odes := [("w", (.bin "*" (.num "0.04") (.bin "-" (.num "7.5") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "5.0")) (.cmp "<" (.var "w") (.num "6.9")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31")))
          next := ["RAMP", "GEN", "STOP"] },
        {
          name := "GEN"
          odes := [("w", (.bin "*" (.num "0.05") (.bin "-" (.num "12.1") (.var "w"))))]
          guard := (.cmp ">=" (.var "w") (.num "6.9"))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31")))
          next := ["GEN"] },
        {
          name := "STOP"
          odes := [("w", (.bin "*" (.neg (.num "0.1")) (.var "w")))]
          guard := (.cmp "<" (.var "w") (.num "2.0"))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31")))
          next := ["STOP"] } ] }
    invariants := [
      ("SPINUP", (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_w") (.num "12.705")))),
      ("RAMP", (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_w") (.num "12.705")))),
      ("GEN", (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_w") (.num "12.705")))),
      ("STOP", (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_w") (.num "12.705"))))] }

end RelCertifier.Parse
