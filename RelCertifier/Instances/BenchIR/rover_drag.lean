/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_drag` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_drag/input.txt` (do not edit). -/
def rover_drag_IR : PProblem :=
  {
    name := "rover_drag"
    lambdaMin := "1.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("vx", (.bin "-" (.num "0.05") (.bin "*" (.num "0.3") (.bin "*" (.var "vx") (.var "vx")))))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.21")))
          evolve := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.4")))
          next := ["Cruise"] } ] }
    R := {
      stateVars := ["vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Track"
          odes := [("vx", (.bin "-" (.num "0.05") (.bin "*" (.num "0.3") (.bin "*" (.var "vx") (.var "vx")))))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.21")))
          evolve := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.4")))
          next := ["Track"] } ] }
    invariants := [
      ("Cruise", (.cmp "<=" (.bin "-" (.var "R_vx") (.var "L_vx")) (.num "0.05")))] }

end RelCertifier.Parse
