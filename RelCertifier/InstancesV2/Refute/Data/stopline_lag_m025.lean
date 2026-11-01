/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_lag_m025`: a mutant of `stopline_lag` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (+ (+ (* 6.0 L_p) (* 1.8 L_v)) (* 1 (* (- L_v (* 0.3 L_b)) (- L_v (* 0.3 L_b))))) (+ (+ (* 6 R_p) (* 1 (* R_v R_v))) 14.4)) [<=->>=]` of `benchmarks/suite_v2/stopline_lag`; file `benchmarks/refute_mutants/stopline_lag_m025/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/stopline_lag_m025/input.txt` (do not edit). -/
def stopline_lag_m025_IRm : PProblem :=
  {
    name := "stopline_lag"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "v", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "b"))))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "3.0") (.var "b"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["p", "v", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0"))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "3.0"))),
            ("b", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0")))
          next := ["STOP"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "L_b") (.num "0.0")))),
      ("BRAKE", (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.num "6.0") (.var "L_p")) (.bin "*" (.num "1.8") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b")))))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_p")) (.bin "*" (.num "1") (.bin "*" (.var "R_v") (.var "R_v")))) (.num "14.4"))))),
      ("STOP", (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.num "6.0") (.var "L_p")) (.bin "*" (.num "1.8") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b")))))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_p")) (.bin "*" (.num "1") (.bin "*" (.var "R_v") (.var "R_v")))) (.num "14.4")))))] }

/-- The finder's witness (kind C). -/
def stopline_lag_m025_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(101 : ℚ), (1 : ℚ), (0 : ℚ)],
    wR := [(101 : ℚ), (1 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
