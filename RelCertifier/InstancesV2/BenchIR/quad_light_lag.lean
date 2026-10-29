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
    lambdaMin := "1.2"
    lambdaMax := "1.2"
    L := {
      stateVars := ["h", "w", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.var "a") (.bin "*" (.num "6.13125") (.var "w")))),
            ("a", (.bin "*" (.num "10.0") (.bin "-" (.num "14.715") (.var "a"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          next := ["CLIMB"] } ] }
    R := {
      stateVars := ["h", "w", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.var "a") (.bin "*" (.num "4.905") (.var "w")))),
            ("a", (.bin "*" (.num "10.0") (.bin "-" (.num "9.81") (.var "a"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          next := ["CLIMB"] } ] }
    invariants := [
      ("CLIMB", (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "-" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.var "L_w")) (.bin "*" (.num "0.1") (.var "L_a"))) (.bin "+" (.bin "+" (.bin "*" (.num "1.25") (.var "R_w")) (.bin "*" (.num "0.125") (.var "R_a"))) (.num "0.14525"))) (.bin "*" (.num "6.13125") (.num "0.45")))) (.cmp "<=" (.bin "*" (.neg (.num "6.13125")) (.num "0.45")) (.bin "-" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.var "L_w")) (.bin "*" (.num "0.1") (.var "L_a"))) (.bin "+" (.bin "+" (.bin "*" (.num "1.25") (.var "R_w")) (.bin "*" (.num "0.125") (.var "R_a"))) (.num "0.14525"))))))] }

end RelCertifier.Parse
