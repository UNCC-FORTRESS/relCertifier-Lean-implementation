/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tunnel_jetfan_pairout` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tunnel_jetfan_pairout`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/tunnel_jetfan_pairout/input.txt` (do not edit). -/
def tunnel_jetfan_pairout_IRv2 : PProblem :=
  {
    name := "tunnel_jetfan_pairout"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "u", "c"]
      epsilon := "1"
      modes := [
        {
          name := "NORMAL"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.018") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "0.1583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "600")) (.cmp "<=" (.var "c") (.num "100"))) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          next := ["NORMAL", "FIRE"] },
        {
          name := "FIRE"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.072") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "1.2583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "600")) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          next := ["FIRE"] } ] }
    R := {
      stateVars := ["t", "u", "c"]
      epsilon := "1"
      modes := [
        {
          name := "NORMAL"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.0225") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "0.1583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "600")) (.cmp "<=" (.var "c") (.num "100"))) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          next := ["NORMAL", "FIRE"] },
        {
          name := "FIRE"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.09") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "1.2583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "600")) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "3.2"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "630")))
          next := ["FIRE"] } ] }
    invariants := [
      ("NORMAL", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "R_u") (.bin "+" (.var "L_u") (.num "0.5")))) (.cmp "<=" (.var "R_c") (.bin "+" (.var "L_c") (.num "0")))) (.cmp "<=" (.var "L_c") (.bin "+" (.var "R_c") (.num "30"))))),
      ("FIRE", (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_u") (.var "R_u"))))] }

end RelCertifier.Parse
