/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bottling_fill_strainer` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bottling_fill_strainer`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/bottling_fill_strainer/input.txt` (do not edit). -/
def bottling_fill_strainer_IRv2 : PProblem :=
  {
    name := "bottling_fill_strainer"
    lambdaMin := "0.8"
    lambdaMax := "1.0"
    L := {
      stateVars := ["V", "u"]
      epsilon := "0.005"
      modes := [
        {
          name := "FILL"
          odes := [("V", (.bin "*" (.num "170") (.var "u"))),
            ("u", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp "<" (.var "V") (.num "994.0")) (.cmp ">=" (.var "u") (.num "1.0"))) (.cmp ">=" (.var "V") (.num "0.0"))) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "V") (.num "0.0")) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          next := ["FILL", "CLOSE"] },
        {
          name := "CLOSE"
          odes := [("V", (.bin "*" (.num "170") (.var "u"))),
            ("u", (.bin "*" (.neg (.num "25")) (.var "u")))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "V") (.num "994.0")) (.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "6.8") (.var "u"))) (.num "1060.0"))) (.cmp ">=" (.var "V") (.num "0.0"))) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "V") (.num "0.0")) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          next := ["CLOSE"] } ] }
    R := {
      stateVars := ["V", "u"]
      epsilon := "0.005"
      modes := [
        {
          name := "FILL"
          odes := [("V", (.bin "*" (.num "200") (.var "u"))),
            ("u", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.cmp "<" (.var "V") (.num "994.0")) (.cmp ">=" (.var "u") (.num "1.0"))) (.cmp ">=" (.var "V") (.num "0.0"))) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "V") (.num "0.0")) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          next := ["FILL", "CLOSE"] },
        {
          name := "CLOSE"
          odes := [("V", (.bin "*" (.num "200") (.var "u"))),
            ("u", (.bin "*" (.neg (.num "25")) (.var "u")))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "V") (.num "994.0")) (.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "8.0") (.var "u"))) (.num "1060.0"))) (.cmp ">=" (.var "V") (.num "0.0"))) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "V") (.num "0.0")) (.cmp "<=" (.var "V") (.num "1060.0"))) (.cmp ">=" (.var "u") (.num "0.0"))) (.cmp "<=" (.var "u") (.num "1.0")))
          next := ["CLOSE"] } ] }
    invariants := [
      ("FILL", (.and (.and (.and (.cmp "<=" (.bin "+" (.var "L_V") (.bin "*" (.num "6.8") (.var "L_u"))) (.bin "+" (.bin "+" (.var "R_V") (.bin "*" (.num "8") (.var "R_u"))) (.neg (.num "1.2")))) (.cmp "<=" (.bin "+" (.bin "+" (.var "R_V") (.bin "*" (.num "8") (.var "R_u"))) (.neg (.num "1.2"))) (.bin "+" (.var "L_V") (.bin "*" (.num "6.8") (.var "L_u"))))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "L_V") (.var "R_V")))),
      ("CLOSE", (.and (.and (.and (.cmp "<=" (.bin "+" (.var "L_V") (.bin "*" (.num "6.8") (.var "L_u"))) (.bin "+" (.bin "+" (.var "R_V") (.bin "*" (.num "8") (.var "R_u"))) (.neg (.num "1.2")))) (.cmp "<=" (.bin "+" (.bin "+" (.var "R_V") (.bin "*" (.num "8") (.var "R_u"))) (.neg (.num "1.2"))) (.bin "+" (.var "L_V") (.bin "*" (.num "6.8") (.var "L_u"))))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "L_V") (.var "R_V"))))] }

end RelCertifier.Parse
