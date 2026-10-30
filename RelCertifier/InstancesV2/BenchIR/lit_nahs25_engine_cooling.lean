/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_engine_cooling` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_engine_cooling`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/lit_nahs25_engine_cooling/input.txt` (do not edit). -/
def lit_nahs25_engine_cooling_IRv2 : PProblem :=
  {
    name := "lit_nahs25_engine_cooling"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["temp"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cool"
          odes := [("temp", (.bin "-" (.num "0.0") (.num "0.5")))]
          guard := (.cmp ">" (.var "temp") (.num "99.7"))
          evolve := (.cmp ">=" (.var "temp") (.num "0.0"))
          next := ["Cool", "Heat"] },
        {
          name := "Heat"
          odes := [("temp", (.num "1.0"))]
          guard := (.cmp "<=" (.var "temp") (.num "100.3"))
          evolve := (.cmp ">=" (.var "temp") (.num "0.0"))
          next := ["Cool", "Heat"] } ] }
    R := {
      stateVars := ["temp"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cool"
          odes := [("temp", (.bin "-" (.num "0.0") (.num "0.5")))]
          guard := (.cmp ">=" (.var "temp") (.num "100.0"))
          evolve := (.cmp ">=" (.var "temp") (.num "0.0"))
          next := ["Cool", "Heat"] },
        {
          name := "Heat"
          odes := [("temp", (.num "1.0"))]
          guard := (.cmp "<=" (.var "temp") (.num "100.0"))
          evolve := (.cmp ">=" (.var "temp") (.num "0.0"))
          next := ["Cool", "Heat"] } ] }
    invariants := [
      ("Cool", (.and (.cmp "<=" (.var "L_temp") (.bin "+" (.var "R_temp") (.num "0.3"))) (.cmp "<=" (.var "R_temp") (.bin "+" (.var "L_temp") (.num "0.3"))))),
      ("Heat", (.and (.cmp "<=" (.var "L_temp") (.bin "+" (.var "R_temp") (.num "0.3"))) (.cmp "<=" (.var "R_temp") (.bin "+" (.var "L_temp") (.num "0.3")))))]
    prelanding := true }

end RelCertifier.Parse
