/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_profiles_m032`: a mutant of `platoon_profiles` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(>= L_g 5.0) [>=-><=]` of `benchmarks/suite_v2/platoon_profiles`; file `benchmarks/refute_mutants/platoon_profiles_m032/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/platoon_profiles_m032/input.txt` (do not edit). -/
def platoon_profiles_m032_IRm : PProblem :=
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
      ("SPORT", (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.4") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.14"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.4") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.14"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.45") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.5")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.bin "*" (.num "1.2") (.var "R_r"))) (.bin "*" (.num "0.45") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.5"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "-" (.num "0.0") (.num "3.34")))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "3.34"))) (.cmp "<=" (.var "L_g") (.num "5.0"))) (.cmp ">=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0"))))] }

/-- The finder's witness (kind B). -/
def platoon_profiles_m032_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 6,
    wL := [(5 : ℚ), (226/125 : ℚ), (0 : ℚ)],
    wR := [(83/50 : ℚ), (167/100 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
