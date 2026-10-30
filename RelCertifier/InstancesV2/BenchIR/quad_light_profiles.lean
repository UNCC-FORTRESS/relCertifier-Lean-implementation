/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_profiles` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_profiles`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/quad_light_profiles/input.txt` (do not edit). -/
def quad_light_profiles_IRv2 : PProblem :=
  {
    name := "quad_light_profiles"
    lambdaMin := "1.15"
    lambdaMax := "1.25"
    L := {
      stateVars := ["h", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "ECO"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "12.2625") (.bin "*" (.num "6.13125") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["ECO", "NORMAL", "SPORT"] },
        {
          name := "NORMAL"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "14.715") (.bin "*" (.num "6.13125") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["NORMAL", "ECO", "SPORT"] },
        {
          name := "SPORT"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "17.780625") (.bin "*" (.num "6.13125") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["SPORT", "ECO", "NORMAL"] } ] }
    R := {
      stateVars := ["h", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "9.81") (.bin "*" (.num "4.905") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["NORMAL", "ECO", "SPORT"] },
        {
          name := "ECO"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "7.848") (.bin "*" (.num "4.905") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["ECO", "NORMAL", "SPORT"] },
        {
          name := "SPORT"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.num "12.2625") (.bin "*" (.num "4.905") (.var "w"))))]
          guard := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          evolve := (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "3.0")))
          next := ["SPORT", "NORMAL", "ECO"] } ] }
    invariants := [
      ("ECO", (.and (.and (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.76")))) (.cmp "<=" (.bin "*" (.num "1.16") (.var "R_w")) (.var "L_w"))) (.cmp "<=" (.var "L_w") (.num "2.9"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.8"))) (.num "0.0")))),
      ("NORMAL", (.and (.and (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.76")))) (.cmp "<=" (.bin "*" (.num "1.16") (.var "R_w")) (.var "L_w"))) (.cmp "<=" (.var "L_w") (.num "2.9"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.8"))) (.num "0.0")))),
      ("SPORT", (.and (.and (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.76")))) (.cmp "<=" (.bin "*" (.num "1.16") (.var "R_w")) (.var "L_w"))) (.cmp "<=" (.var "L_w") (.num "2.9"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.bin "-" (.var "L_w") (.bin "*" (.num "1.25") (.var "R_w")))) (.bin "*" (.num "6.13125") (.num "0.8"))) (.num "0.0"))))] }

end RelCertifier.Parse
