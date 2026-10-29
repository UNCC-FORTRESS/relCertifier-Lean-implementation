/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_latency_m049`: a mutant of `platoon_latency` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(>= L_e (- 0.0 0.5)) [L_e->R_e]` of `benchmarks/suite_v2/platoon_latency`; file `benchmarks/refute_mutants/platoon_latency_m049/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/platoon_latency_m049/input.txt` (do not edit). -/
def platoon_latency_m049_IRm : PProblem :=
  {
    name := "platoon_latency"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["g", "r", "e"]
      epsilon := "0.1"
      modes := [
        {
          name := "CACC_UP"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "-" (.var "e") (.bin "*" (.num "0.125") (.bin "-" (.var "g") (.num "20.0")))) (.bin "*" (.num "0.75") (.var "r")))),
            ("e", (.bin "-" (.num "2.5") (.bin "*" (.num "5.0") (.var "e"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.var "e") (.num "-20.0"))) (.cmp "<=" (.var "e") (.num "20.0")))
          next := ["CACC_UP", "CACC_DN", "AEB"] },
        {
          name := "CACC_DN"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "-" (.var "e") (.bin "*" (.num "0.125") (.bin "-" (.var "g") (.num "20.0")))) (.bin "*" (.num "0.75") (.var "r")))),
            ("e", (.bin "-" (.bin "-" (.num "0.0") (.num "2.5")) (.bin "*" (.num "5.0") (.var "e"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.var "e") (.num "-20.0"))) (.cmp "<=" (.var "e") (.num "20.0")))
          next := ["CACC_UP", "CACC_DN", "AEB"] },
        {
          name := "AEB"
          odes := [("g", (.var "r")),
            ("r", (.bin "*" (.num "-0.5") (.var "r"))),
            ("e", (.num "0.0"))]
          guard := (.and (.and (.cmp "<" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.var "e") (.num "-20.0"))) (.cmp "<=" (.var "e") (.num "20.0")))
          next := ["AEB"] } ] }
    R := {
      stateVars := ["g", "r", "e"]
      epsilon := "0.1"
      modes := [
        {
          name := "CACC"
          odes := [("g", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g") (.num "20.0"))) (.bin "*" (.num "0.75") (.var "r")))),
            ("e", (.num "0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "r") (.num "-10.0")) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.var "e") (.num "-20.0"))) (.cmp "<=" (.var "e") (.num "20.0")))
          next := ["CACC", "AEB"] },
        {
          name := "AEB"
          odes := [("g", (.var "r")),
            ("r", (.bin "*" (.num "-0.5") (.var "r"))),
            ("e", (.num "0"))]
          guard := (.and (.and (.cmp "<" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")) (.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0"))) (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))) (.cmp ">=" (.var "e") (.num "-20.0"))) (.cmp "<=" (.var "e") (.num "20.0")))
          next := ["AEB"] } ] }
    invariants := [
      ("CACC_UP", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "2.0")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "2.0"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "-" (.num "0.0") (.num "4.0")))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "4.0"))) (.cmp ">=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "60.0"))) (.cmp ">=" (.var "L_g") (.num "5.0"))) (.cmp ">=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0"))) (.cmp ">=" (.var "R_e") (.bin "-" (.num "0.0") (.num "0.5")))) (.cmp "<=" (.var "L_e") (.num "0.5")))),
      ("CACC_DN", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "1.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.25") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "1.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.bin "-" (.num "0.0") (.num "2.0")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r") (.var "R_r")) (.bin "*" (.num "0.5") (.bin "-" (.var "L_g") (.var "R_g")))) (.num "2.0"))) (.cmp ">=" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "-" (.num "0.0") (.num "4.0")))) (.cmp "<=" (.bin "-" (.var "L_g") (.var "R_g")) (.num "4.0"))) (.cmp ">=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "5.0"))) (.cmp "<=" (.bin "+" (.var "R_g") (.bin "*" (.num "2.0") (.var "R_r"))) (.num "60.0"))) (.cmp ">=" (.var "L_g") (.num "5.0"))) (.cmp ">=" (.bin "+" (.var "L_g") (.bin "*" (.num "2.0") (.var "L_r"))) (.num "5.0"))) (.cmp ">=" (.var "R_e") (.bin "-" (.num "0.0") (.num "0.5")))) (.cmp "<=" (.var "L_e") (.num "0.5")))),
      ("AEB", (.and (.and (.and (.cmp ">=" (.bin "-" (.var "L_r") (.var "R_r")) (.num "0.0")) (.cmp "<=" (.bin "-" (.var "L_r") (.var "R_r")) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "*" (.num "2.0") (.bin "-" (.var "L_r") (.var "R_r")))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_g") (.var "R_g")) (.bin "*" (.num "2.0") (.bin "-" (.var "L_r") (.var "R_r")))) (.num "0.0"))))] }

/-- The finder's witness (kind B). -/
def platoon_latency_m049_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 9,
    wL := [(5 : ℚ), (0 : ℚ), (-19/8 : ℚ)],
    wR := [(1 : ℚ), (2 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
