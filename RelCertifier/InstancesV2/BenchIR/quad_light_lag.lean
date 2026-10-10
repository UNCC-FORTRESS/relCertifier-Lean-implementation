/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_lag`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/quad_light_lag/input.txt` (do not edit). -/
def quad_light_lag_IRv2 : PProblem :=
  {
    name := "quad_light_lag"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["w", "a"]
      epsilon := "2.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("w", (.bin "-" (.var "a") (.bin "*" (.num "1.25") (.bin "*" (.var "w") (.var "w"))))),
            ("a", (.bin "*" (.num "5.0") (.bin "-" (.num "7.45") (.var "a"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "2.5"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "7.45")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "7.45")))
          next := ["CLIMB"] } ] }
    R := {
      stateVars := ["w", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("w", (.bin "-" (.num "4.0") (.bin "*" (.var "w") (.var "w")))),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "2.6")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "7.45")))
          next := ["CLIMB"] } ] }
    invariants := [
      ("CLIMB", (.cmp "<=" (.bin "+" (.var "L_a") (.bin "*" (.num "5.0") (.var "L_w"))) (.bin "+" (.bin "*" (.num "5.0") (.var "R_w")) (.num "12.45"))))] }

end RelCertifier.Parse
