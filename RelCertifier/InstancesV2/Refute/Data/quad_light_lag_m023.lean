/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag_m023`: a mutant of `quad_light_lag` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (* (- 6.13125) 0.16) (- (+ (* 6.13125 (- L_h R_h)) L_w (* 0.1 L_a)) (+ (* 1.25 R_w) (* 0.125 R_a) 0.14525))) [R_w->L_w]` of `benchmarks/suite_v2/quad_light_lag`; file `benchmarks/refute_mutants/quad_light_lag_m023/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/quad_light_lag_m023/input.txt` (do not edit). -/
def quad_light_lag_m023_IRm : PProblem :=
  {
    name := "quad_light_lag"
    lambdaMin := "1.2"
    lambdaMax := "1.2"
    L := {
      stateVars := ["h", "w", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.var "a") (.bin "*" (.num "6.13125") (.var "w")))),
            ("a", (.bin "*" (.num "10.0") (.bin "-" (.num "14.715") (.var "a"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.4"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.4"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "14.715")))
          next := ["CLIMB"] } ] }
    R := {
      stateVars := ["h", "w", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "CLIMB"
          odes := [("h", (.var "w")),
            ("w", (.bin "-" (.var "a") (.bin "*" (.num "4.905") (.var "w")))),
            ("a", (.bin "*" (.num "10.0") (.bin "-" (.num "9.81") (.var "a"))))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "9.81")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp ">=" (.var "w") (.num "0.0"))) (.cmp "<=" (.var "w") (.num "2.0"))) (.cmp ">=" (.var "a") (.num "0.0"))) (.cmp "<=" (.var "a") (.num "9.81")))
          next := ["CLIMB"] } ] }
    invariants := [
      ("CLIMB", (.and (.and (.and (.cmp "<=" (.bin "-" (.var "R_h") (.var "L_h")) (.num "0.8")) (.cmp "<=" (.bin "-" (.var "L_h") (.var "R_h")) (.num "0.8"))) (.cmp "<=" (.bin "-" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.var "L_w")) (.bin "*" (.num "0.1") (.var "L_a"))) (.bin "+" (.bin "+" (.bin "*" (.num "1.25") (.var "R_w")) (.bin "*" (.num "0.125") (.var "R_a"))) (.num "0.14525"))) (.bin "*" (.num "6.13125") (.num "0.16")))) (.cmp "<=" (.bin "*" (.neg (.num "6.13125")) (.num "0.16")) (.bin "-" (.bin "+" (.bin "+" (.bin "*" (.num "6.13125") (.bin "-" (.var "L_h") (.var "R_h"))) (.var "L_w")) (.bin "*" (.num "0.1") (.var "L_a"))) (.bin "+" (.bin "+" (.bin "*" (.num "1.25") (.var "L_w")) (.bin "*" (.num "0.125") (.var "R_a"))) (.num "0.14525"))))))] }

/-- The finder's witness (kind B). -/
def quad_light_lag_m023_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 3,
    wL := [(436/1175 : ℚ), (436/1175 : ℚ), (134833/9400 : ℚ)],
    wR := [(67392/128075 : ℚ), (0 : ℚ), (981/100 : ℚ)] }

end RelCertifier.Refute
