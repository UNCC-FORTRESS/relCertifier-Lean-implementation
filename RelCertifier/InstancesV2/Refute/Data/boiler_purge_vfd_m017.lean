/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `boiler_purge_vfd_m017`: a mutant of `boiler_purge_vfd` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant MCO `(<= 0.0 L_e) [del]` of `benchmarks/suite_v2/boiler_purge_vfd`; file `benchmarks/refute_mutants/boiler_purge_vfd_m017/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/boiler_purge_vfd_m017/input.txt` (do not edit). -/
def boiler_purge_vfd_m017_IRm : PProblem :=
  {
    name := "boiler_purge_vfd"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "p", "e"]
      epsilon := "1.0"
      modes := [
        {
          name := "PURGE"
          odes := [("v", (.num "0.016")),
            ("p", (.num "0.0")),
            ("e", (.num "0.0"))]
          guard := (.cmp "<" (.var "v") (.num "5.0"))
          evolve := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp ">=" (.var "p") (.num "-1.0"))) (.cmp "<=" (.var "p") (.num "16.0")))
          next := ["PURGE", "FIRE"] },
        {
          name := "FIRE"
          odes := [("v", (.num "0.0")),
            ("p", (.bin "*" (.num "0.000555555556") (.bin "-" (.bin "-" (.num "10.0") (.var "e")) (.var "p")))),
            ("e", (.num "0.0"))]
          guard := (.cmp ">=" (.var "v") (.num "5.0"))
          evolve := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp ">=" (.var "p") (.num "-1.0"))) (.cmp "<=" (.var "p") (.num "16.0")))
          next := ["FIRE"] } ] }
    R := {
      stateVars := ["v", "p", "e"]
      epsilon := "1.0"
      modes := [
        {
          name := "PURGE"
          odes := [("v", (.num "0.01")),
            ("p", (.num "0.0")),
            ("e", (.num "0.0"))]
          guard := (.cmp "<" (.var "v") (.num "5.0"))
          evolve := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp ">=" (.var "p") (.num "-1.0"))) (.cmp "<=" (.var "p") (.num "16.0")))
          next := ["PURGE", "FIRE"] },
        {
          name := "FIRE"
          odes := [("v", (.num "0.0")),
            ("p", (.bin "*" (.num "0.000555555556") (.bin "-" (.num "10.0") (.var "p")))),
            ("e", (.num "0.0"))]
          guard := (.cmp ">=" (.var "v") (.num "5.0"))
          evolve := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp ">=" (.var "p") (.num "-1.0"))) (.cmp "<=" (.var "p") (.num "16.0")))
          next := ["FIRE"] } ] }
    invariants := [
      ("PURGE", (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "*" (.num "0.625") (.var "L_v")) (.var "R_v"))) (.cmp "<=" (.var "L_e") (.num "0.1962")))),
      ("FIRE", (.and (.and (.and (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "0.0"))) (.cmp "<=" (.var "R_p") (.bin "+" (.var "L_p") (.var "L_e")))) (.cmp "<=" (.bin "*" (.num "0.625") (.var "L_v")) (.var "R_v"))) (.cmp "<=" (.var "L_e") (.num "0.1962"))))] }

/-- The finder's witness (kind C). -/
def boiler_purge_vfd_m017_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 0, k := 0,
    wL := [(5 : ℚ), (0 : ℚ), (-3 : ℚ)],
    wR := [(25/8 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
