/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag_m019`: a mutant of `stopline_drag` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_c 0.0) [<=->>=]` of `benchmarks/suite_v2/stopline_drag`; file `benchmarks/refute_mutants/stopline_drag_m019/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/stopline_drag_m019/input.txt` (do not edit). -/
def stopline_drag_m019_IRm : PProblem :=
  {
    name := "stopline_drag"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "v", "b", "c"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "c"))))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("v", (.bin "-" (.bin "-" (.bin "-" (.num "0.0") (.var "b")) (.bin "*" (.num "0.003") (.bin "*" (.var "v") (.var "v")))) (.num "0.2"))),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "2.7") (.var "c"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("c", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["p", "v", "b", "c"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "c"))))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "2.7") (.var "c"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("c", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0")))
          next := ["STOP"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "L_c") (.num "0.0"))) (.cmp "<=" (.var "R_b") (.num "0.0"))) (.cmp "<=" (.var "R_c") (.num "0.0"))) (.cmp ">=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "L_c") (.num "0.0"))) (.cmp ">=" (.var "R_b") (.num "0.0"))) (.cmp ">=" (.var "R_c") (.num "0.0")))),
      ("BRAKE", (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.89") (.var "L_v"))) (.bin "*" (.num "0.081") (.var "L_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c"))) (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c")))))) (.bin "+" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "R_p")) (.bin "*" (.num "1.89") (.var "R_v"))) (.bin "*" (.num "0.081") (.var "R_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c"))) (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c")))))) (.num "0.0")))) (.cmp "<=" (.var "L_b") (.num "2.7"))) (.cmp "<=" (.var "L_c") (.num "2.7")))),
      ("STOP", (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.89") (.var "L_v"))) (.bin "*" (.num "0.081") (.var "L_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c"))) (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c")))))) (.bin "+" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "R_p")) (.bin "*" (.num "1.89") (.var "R_v"))) (.bin "*" (.num "0.081") (.var "R_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c"))) (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c")))))) (.num "0.0")))))] }

/-- The finder's witness (kind C). -/
def stopline_drag_m019_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(101 : ℚ), (1 : ℚ), (0 : ℚ), (11/4 : ℚ)],
    wR := [(101 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
