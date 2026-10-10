/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_linkloss` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_delay_linkloss`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/platoon_delay_linkloss/input.txt` (do not edit). -/
def platoon_delay_linkloss_IRv2 : PProblem :=
  {
    name := "platoon_delay_linkloss"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["g"]
      epsilon := "2.0"
      modes := [
        {
          name := "FOLLOW"
          odes := [("g", (.bin "*" (.num "-0.5") (.bin "-" (.var "g") (.num "29.0"))))]
          guard := (.and (.cmp ">=" (.var "g") (.num "21.0")) (.cmp "<" (.var "g") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["CATCH", "FOLLOW", "LOST"] },
        {
          name := "CATCH"
          odes := [("g", (.bin "*" (.num "-0.6") (.bin "-" (.var "g") (.num "29.0"))))]
          guard := (.cmp ">=" (.var "g") (.num "30.0"))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["FOLLOW", "CATCH", "LOST"] },
        {
          name := "LOST"
          odes := [("g", (.bin "*" (.num "-0.5") (.bin "-" (.var "g") (.num "35.0"))))]
          guard := (.and (.cmp ">=" (.var "g") (.num "21.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["LOST"] } ] }
    R := {
      stateVars := ["g"]
      epsilon := "1.0"
      modes := [
        {
          name := "FOLLOW"
          odes := [("g", (.bin "*" (.num "-0.5") (.bin "-" (.var "g") (.num "30.0"))))]
          guard := (.and (.cmp ">=" (.var "g") (.num "20.0")) (.cmp "<" (.var "g") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["CATCH", "FOLLOW", "BRAKE"] },
        {
          name := "CATCH"
          odes := [("g", (.bin "*" (.num "-0.6") (.bin "-" (.var "g") (.num "30.0"))))]
          guard := (.cmp ">=" (.var "g") (.num "30.0"))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["FOLLOW", "CATCH"] },
        {
          name := "BRAKE"
          odes := [("g", (.num "1.5"))]
          guard := (.cmp "<" (.var "g") (.num "20.0"))
          evolve := (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
          next := ["BRAKE", "FOLLOW"] } ] }
    invariants := [
      ("FOLLOW", (.and (.cmp "<=" (.var "L_g") (.bin "+" (.var "R_g") (.num "1.0"))) (.cmp "<=" (.var "R_g") (.bin "+" (.var "L_g") (.num "3.0"))))),
      ("CATCH", (.and (.cmp "<=" (.var "L_g") (.bin "+" (.var "R_g") (.num "1.0"))) (.cmp "<=" (.var "R_g") (.bin "+" (.var "L_g") (.num "3.0"))))),
      ("LOST", (.and (.cmp "<=" (.bin "*" (.num "0.55") (.var "L_g")) (.bin "-" (.var "R_g") (.num "8.45"))) (.cmp "<=" (.var "R_g") (.bin "+" (.var "L_g") (.num "3.0")))))] }

end RelCertifier.Parse
