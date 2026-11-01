/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_rover_2to5_m018`: a mutant of `stopline_rover_2to5` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_psi 0.35) [<=->>=]` of `benchmarks/suite_v2/stopline_rover_2to5`; file `benchmarks/refute_mutants/stopline_rover_2to5_m018/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/stopline_rover_2to5_m018/input.txt` (do not edit). -/
def stopline_rover_2to5_m018_IRm : PProblem :=
  {
    name := "stopline_rover_2to5"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "s", "v", "b", "psi"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi")))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "3.0") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("s", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("psi", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["p", "v"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "3.0")))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0")))
          next := ["STOP"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("BRAKE", (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "L_p")) (.bin "*" (.num "1.8") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b")))))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_p")) (.bin "*" (.num "1") (.bin "*" (.var "R_v") (.var "R_v")))) (.num "14.4")))) (.cmp ">=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("STOP", (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "L_p")) (.bin "*" (.num "1.8") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b")))))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_p")) (.bin "*" (.num "1") (.bin "*" (.var "R_v") (.var "R_v")))) (.num "14.4")))) (.cmp ">=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_s") (.var "L_p"))))] }

/-- The finder's witness (kind B). -/
def stopline_rover_2to5_m018_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 1, k := 2,
    wL := [(101 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (7/20 : ℚ)],
    wR := [(101 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
