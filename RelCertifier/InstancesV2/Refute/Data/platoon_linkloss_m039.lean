/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_linkloss_m039`: a mutant of `platoon_linkloss` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(>= (+ L_g (* 2.0 L_r)) 5.0) [>=-><=]` of `benchmarks/suite_v2/platoon_linkloss`; file `benchmarks/refute_mutants/platoon_linkloss_m039/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/platoon_linkloss_m039/input.txt` (do not edit). -/
def platoon_linkloss_m039_IRm : PProblem :=
  {
    name := "platoon_linkloss"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["g", "r"]
      epsilon := "0.2"
      modes := [
        {
          name := "CACC"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g") (.num "20.0"))) (.bin "*" (.num "0.75") (.var "r"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["CACC", "ACC", "AEB"] },
        {
          name := "ACC"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g") (.num "35.0"))) (.bin "*" (.num "0.75") (.var "r"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["ACC", "CACC", "AEB"] },
        {
          name := "AEB"
          odes := [("g", (.var "r")),
            ("r", (.bin "*" (.num "-0.5") (.var "r")))]
          guard := (.and (.and (.cmp "<" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["AEB"] } ] }
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
          next := ["CACC", "AEB"] },
        {
          name := "AEB"
          odes := [("g", (.var "r")),
            ("r", (.bin "*" (.num "-0.5") (.var "r")))]
          guard := (.and (.and (.cmp "<" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0")))
          next := ["AEB"] } ] }
    invariants := [
      ("CACC", (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "0.0")) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "3.75"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "7.5"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "0.0"))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "15.0"))) (.cmp ">=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "5.0"))) (.cmp ">=" (.var "L_g") (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0")))),
      ("ACC", (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "0.0")) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "3.75"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "7.5"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "0.0"))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "15.0"))) (.cmp ">=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "5.0"))) (.cmp ">=" (.var "L_g") (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0")))),
      ("AEB", (.and (.and (.and (.cmp ">=" (.bin "-" (.var "L_r") (.var "R_r")) (.num "0.0")) (.cmp "<=" (.bin "-" (.var "L_r") (.var "R_r")) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "*" (.num "2.0") (.bin "-" (.var "L_r") (.var "R_r")))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "*" (.num "2.0") (.bin "-" (.var "L_r") (.var "R_r")))) (.num "0.0"))))] }

/-- The finder's witness (kind B). -/
def platoon_linkloss_m039_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 8,
    wL := [(5 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(5 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
