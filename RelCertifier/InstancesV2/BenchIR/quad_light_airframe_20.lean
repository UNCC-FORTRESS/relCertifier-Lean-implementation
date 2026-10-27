/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_airframe_20`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/quad_light_airframe_20/input.txt` (do not edit). -/
def quad_light_airframe_20_IRv2 : PProblem :=
  {
    name := "quad_light_airframe_20"
    lambdaMin := "1.2"
    lambdaMax := "1.2"
    L := {
      stateVars := ["h", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "14.715") (.bin "*" (.num "6.13125") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.4")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.4")))
          next := ["CLIMB"] } ] }
    R := {
      stateVars := ["h", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "9.81") (.bin "*" (.num "4.905") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.0")))
          next := ["CLIMB"] } ] }
    invariants := [
      ("CLIMB", (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.num "0.1")) (.bin "*" (.num "6.13125") (.num "0.8")))) (.cmp "<=" (.bin "*" (.num "1.2") (.var "R_w")) (.var "L_w"))))] }

end RelCertifier.Parse
