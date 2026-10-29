/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `flaps_slow_approach` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py flaps_slow_approach`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/flaps_slow_approach/input.txt` (do not edit). -/
def flaps_slow_approach_IRv2 : PProblem :=
  {
    name := "flaps_slow_approach"
    lambdaMin := "0.5"
    lambdaMax := "1.0"
    L := {
      stateVars := ["f", "V"]
      epsilon := "0.1"
      modes := [
        {
          name := "EXT"
          odes := [("f", (.num "0.5")),
            ("V", (.bin "*" (.bin "-" (.num "0.0") (.bin "+" (.num "0.02") (.bin "*" (.num "0.001") (.var "f")))) (.bin "-" (.var "V") (.num "150"))))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "f") (.num "15")) (.cmp ">=" (.var "f") (.num "10"))) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "f") (.num "10")) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          next := ["EXT", "CONF2"] },
        {
          name := "CONF2"
          odes := [("f", (.num "0")),
            ("V", (.bin "*" (.bin "-" (.num "0.0") (.bin "+" (.num "0.02") (.bin "*" (.num "0.001") (.var "f")))) (.bin "-" (.var "V") (.num "150"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "f") (.num "15")) (.cmp ">=" (.var "f") (.num "10"))) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "f") (.num "10")) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          next := ["CONF2"] } ] }
    R := {
      stateVars := ["f", "V"]
      epsilon := "0.1"
      modes := [
        {
          name := "EXT"
          odes := [("f", (.num "1")),
            ("V", (.bin "*" (.bin "-" (.num "0.0") (.bin "+" (.num "0.02") (.bin "*" (.num "0.001") (.var "f")))) (.bin "-" (.var "V") (.num "150"))))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "f") (.num "15")) (.cmp ">=" (.var "f") (.num "10"))) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "f") (.num "10")) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          next := ["EXT", "CONF2"] },
        {
          name := "CONF2"
          odes := [("f", (.num "0")),
            ("V", (.bin "*" (.bin "-" (.num "0.0") (.bin "+" (.num "0.02") (.bin "*" (.num "0.001") (.var "f")))) (.bin "-" (.var "V") (.num "150"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "f") (.num "15")) (.cmp ">=" (.var "f") (.num "10"))) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "f") (.num "10")) (.cmp "<=" (.var "f") (.num "15.1"))) (.cmp ">=" (.var "V") (.num "130"))) (.cmp "<=" (.var "V") (.num "200")))
          next := ["CONF2"] } ] }
    invariants := [
      ("EXT", (.and (.and (.and (.cmp "<=" (.var "L_f") (.var "R_f")) (.cmp "<=" (.var "R_f") (.var "L_f"))) (.cmp "<=" (.var "L_V") (.bin "+" (.var "R_V") (.num "10")))) (.cmp "<=" (.var "R_V") (.bin "+" (.var "L_V") (.num "25"))))),
      ("CONF2", (.and (.and (.and (.cmp "<=" (.var "L_f") (.var "R_f")) (.cmp "<=" (.var "R_f") (.var "L_f"))) (.cmp "<=" (.var "L_V") (.bin "+" (.var "R_V") (.num "10")))) (.cmp "<=" (.var "R_V") (.bin "+" (.var "L_V") (.num "25")))))] }

end RelCertifier.Parse
