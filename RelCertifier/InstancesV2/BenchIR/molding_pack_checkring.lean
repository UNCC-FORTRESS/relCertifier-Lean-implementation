/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `molding_pack_checkring` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py molding_pack_checkring`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/molding_pack_checkring/input.txt` (do not edit). -/
def molding_pack_checkring_IRv2 : PProblem :=
  {
    name := "molding_pack_checkring"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "x", "y"]
      epsilon := "0.05"
      modes := [
        {
          name := "HOLD"
          odes := [("t", (.num "1.0")),
            ("x", (.bin "-" (.bin "*" (.num "10.0") (.bin "-" (.num "500.0") (.var "x"))) (.bin "*" (.num "0.4") (.var "x")))),
            ("y", (.bin "*" (.num "3.0") (.bin "-" (.var "x") (.var "y"))))]
          guard := (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "5.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          next := ["HOLD", "COOL"] },
        {
          name := "COOL"
          odes := [("t", (.num "1.0")),
            ("x", (.bin "*" (.neg (.bin "+" (.num "2.0") (.num "0.4"))) (.var "x"))),
            ("y", (.bin "*" (.neg (.num "0.3")) (.var "y")))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "5.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          next := ["COOL"] } ] }
    R := {
      stateVars := ["t", "x", "y"]
      epsilon := "0.05"
      modes := [
        {
          name := "HOLD"
          odes := [("t", (.num "1.0")),
            ("x", (.bin "-" (.bin "*" (.num "10.0") (.bin "-" (.num "500.0") (.var "x"))) (.bin "*" (.num "0.0") (.var "x")))),
            ("y", (.bin "*" (.num "3.0") (.bin "-" (.var "x") (.var "y"))))]
          guard := (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "5.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          next := ["HOLD", "COOL"] },
        {
          name := "COOL"
          odes := [("t", (.num "1.0")),
            ("x", (.bin "*" (.neg (.bin "+" (.num "2.0") (.num "0.0"))) (.var "x"))),
            ("y", (.bin "*" (.neg (.num "0.3")) (.var "y")))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "5.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "x") (.num "0.0"))) (.cmp "<=" (.var "x") (.num "500.0"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "500.0")))
          next := ["COOL"] } ] }
    invariants := [
      ("HOLD", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "25")))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "25")))) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "25")))) (.cmp "<=" (.var "R_y") (.bin "+" (.var "L_y") (.num "25"))))),
      ("COOL", (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "25")))) (.cmp "<=" (.var "R_y") (.bin "+" (.var "L_y") (.num "25")))))] }

end RelCertifier.Parse
