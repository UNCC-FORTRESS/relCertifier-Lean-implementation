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
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["w"]
      epsilon := "2.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("w", (.bin "-" (.num "9.524") (.bin "*" (.num "1.4") (.bin "*" (.var "w") (.var "w")))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "2.2")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5")))
          next := ["CLIMB"] } ] }
    R := {
      stateVars := ["w"]
      epsilon := "1.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("w", (.bin "-" (.num "4.0") (.bin "*" (.var "w") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.2")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5")))
          next := ["NORMAL", "ECO", "SPORT", "LIMIT"] },
        {
          name := "ECO"
          odes := [("w", (.bin "-" (.num "3.6") (.bin "*" (.var "w") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.2")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5")))
          next := ["ECO", "NORMAL", "LIMIT"] },
        {
          name := "SPORT"
          odes := [("w", (.bin "-" (.num "4.4") (.bin "*" (.var "w") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.2")))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5")))
          next := ["SPORT", "NORMAL", "LIMIT"] },
        {
          name := "LIMIT"
          odes := [("w", (.bin "*" (.num "-2.0") (.var "w")))]
          guard := (.cmp ">" (.var "w") (.num "3.2"))
          evolve := (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "3.5")))
          next := ["LIMIT", "NORMAL"] } ] }
    invariants := [
      ("CLIMB", (.and (.cmp "<=" (.var "L_w") (.bin "+" (.var "R_w") (.num "0.95"))) (.cmp "<=" (.var "R_w") (.bin "+" (.var "L_w") (.num "0.8")))))] }

end RelCertifier.Parse
