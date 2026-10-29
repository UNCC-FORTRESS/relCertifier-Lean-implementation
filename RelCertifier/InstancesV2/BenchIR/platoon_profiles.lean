/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_profiles` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_profiles`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/platoon_profiles/input.txt` (do not edit). -/
def platoon_profiles_IRv2 : PProblem :=
  {
    name := "platoon_profiles"
    lambdaMin := "1.2"
    lambdaMax := "1.2"
    L := {
      stateVars := ["g", "r"]
      epsilon := "0.1"
      modes := [
        {
          name := "SPORT"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-0.18") (.bin "-" (.var "g") (.num "20.0"))) (.bin "*" (.num "0.85") (.var "r"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["SPORT"] } ] }
    R := {
      stateVars := ["g", "r"]
      epsilon := "0.1"
      modes := [
        {
          name := "CACC"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g") (.num "20.0"))) (.bin "*" (.num "0.75") (.var "r"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["CACC"] } ] }
    invariants := [
      ("SPORT", (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.4") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.14"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.4") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.14"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.45") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.5")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.45") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.5"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "-" (.num "0.0") (.num "3.34")))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "3.34"))) (.cmp ">=" (.var "L_g") (.num "5.0"))) (.cmp ">=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0"))))] }

end RelCertifier.Parse
