/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12_m004`: a mutant of `rover3tier_rung12` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (+ (* 3 L_v) L_a) (+ (* 3 R_v) 1.2)) [<=->>=]` of `benchmarks/suite_v2/rover3tier_rung12`; file `benchmarks/refute_mutants/rover3tier_rung12_m004/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover3tier_rung12_m004/input.txt` (do not edit). -/
def rover3tier_rung12_m004_IRm : PProblem :=
  {
    name := "rover3tier_rung12"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "0.8") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.3")) (.cmp "<=" (.var "a") (.num "0.95"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.5")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "-0.3") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.3")) (.cmp "<=" (.var "a") (.num "0.95"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.5")))
          next := ["ACCEL", "COAST"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "0.3"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.5")) (.cmp "<=" (.var "a") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.cmp ">=" (.var "v") (.num "0.6"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.5")) (.cmp "<=" (.var "a") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0")))
          next := ["ACCEL", "COAST"] } ] }
    invariants := [
      ("ACCEL", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5"))) (.cmp ">=" (.bin "+" (.bin "*" (.num "3") (.var "L_v")) (.var "L_a")) (.bin "+" (.bin "*" (.num "3") (.var "R_v")) (.num "1.2"))))),
      ("COAST", (.cmp ">=" (.bin "+" (.bin "*" (.num "3") (.var "L_v")) (.var "L_a")) (.bin "+" (.bin "*" (.num "3") (.var "R_v")) (.num "1.2"))))] }

/-- The finder's witness (kind B). -/
def rover3tier_rung12_m004_wit : RefWitE :=
  { kind := "B", u := 0, m := 1, q0 := 0, k := 0,
    wL := [(1 : ℚ), (3/40 : ℚ), (-9/40 : ℚ)],
    wR := [(21/40 : ℚ), (0 : ℚ), (1/2 : ℚ)] }

end RelCertifier.Refute
