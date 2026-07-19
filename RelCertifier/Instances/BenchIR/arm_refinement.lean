/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_refinement` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_refinement/input.txt` (do not edit). -/
def arm_refinement_IR : PProblem :=
  {
    name := "arm_refinement"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.85")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.85"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "Approach"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "Approach"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Approach", "Return"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4"))))] }

end RelCertifier.Parse
