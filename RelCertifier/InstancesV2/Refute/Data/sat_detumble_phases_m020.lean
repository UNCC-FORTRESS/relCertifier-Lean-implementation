/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_phases_m020`: a mutant of `sat_detumble_phases` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (+ (+ (* (* L_w1 L_w1) 2.0) (* (* L_w2 L_w2) 4.0)) (* (* L_w3 L_w3) 5.0)) (+ (+ (+ (* (* R_w1 R_w1) 2.0) (* (* R_w2 R_w2) 4.0)) (* (* R_w3 R_w3) 5.0)) 0.085)) [L_w3->R_w3]` of `benchmarks/suite_v2/sat_detumble_phases`; file `benchmarks/refute_mutants/sat_detumble_phases_m020/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/sat_detumble_phases_m020/input.txt` (do not edit). -/
def sat_detumble_phases_m020_IRm : PProblem :=
  {
    name := "sat_detumble_phases"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["w1", "w2", "w3", "h"]
      epsilon := "2.0"
      modes := [
        {
          name := "DETUMBLE"
          odes := [("w1", (.bin "-" (.bin "-" (.bin "*" (.num "-0.5") (.bin "*" (.var "w2") (.var "w3"))) (.bin "*" (.num "0.5") (.bin "*" (.var "w2") (.var "h")))) (.bin "*" (.num "0.5") (.var "w1")))),
            ("w2", (.bin "-" (.bin "+" (.bin "*" (.num "0.75") (.bin "*" (.var "w3") (.var "w1"))) (.bin "*" (.num "0.25") (.bin "*" (.var "w1") (.var "h")))) (.bin "*" (.num "0.5") (.var "w2")))),
            ("w3", (.bin "-" (.bin "*" (.num "-0.4") (.bin "*" (.var "w1") (.var "w2"))) (.bin "*" (.num "0.5") (.var "w3")))),
            ("h", (.bin "*" (.num "2.5") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["FINE", "DETUMBLE"] },
        {
          name := "FINE"
          odes := [("w1", (.bin "-" (.bin "-" (.bin "*" (.num "-0.5") (.bin "*" (.var "w2") (.var "w3"))) (.bin "*" (.num "0.5") (.bin "*" (.var "w2") (.var "h")))) (.bin "*" (.num "0.3") (.var "w1")))),
            ("w2", (.bin "-" (.bin "+" (.bin "*" (.num "0.75") (.bin "*" (.var "w3") (.var "w1"))) (.bin "*" (.num "0.25") (.bin "*" (.var "w1") (.var "h")))) (.bin "*" (.num "0.3") (.var "w2")))),
            ("w3", (.bin "-" (.bin "*" (.num "-0.4") (.bin "*" (.var "w1") (.var "w2"))) (.bin "*" (.num "0.3") (.var "w3")))),
            ("h", (.bin "*" (.num "1.5") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "0.2"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["FINE"] } ] }
    R := {
      stateVars := ["w1", "w2", "w3", "h"]
      epsilon := "1.0"
      modes := [
        {
          name := "DETUMBLE"
          odes := [("w1", (.bin "*" (.num "-0.5") (.var "w1"))),
            ("w2", (.bin "*" (.num "-0.5") (.var "w2"))),
            ("w3", (.bin "*" (.num "-0.5") (.var "w3"))),
            ("h", (.bin "*" (.num "2.5") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0"))) (.cmp ">=" (.bin "+" (.var "h") (.bin "*" (.num "5.0") (.var "w3"))) (.num "-2.0"))) (.cmp "<=" (.bin "+" (.var "h") (.bin "*" (.num "5.0") (.var "w3"))) (.num "2.0")))
          next := ["DETUMBLE", "SAFE"] },
        {
          name := "SAFE"
          odes := [("w1", (.num "0")),
            ("w2", (.num "0")),
            ("w3", (.num "0")),
            ("h", (.num "0"))]
          guard := (.cmp ">" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0"))) (.cmp ">=" (.bin "+" (.var "h") (.bin "*" (.num "5.0") (.var "w3"))) (.num "-2.0"))) (.cmp "<=" (.bin "+" (.var "h") (.bin "*" (.num "5.0") (.var "w3"))) (.num "2.0")))
          next := ["SAFE"] } ] }
    invariants := [
      ("DETUMBLE", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "L_w3") (.var "L_w3")) (.num "5.0"))) (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5.0")))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5.0"))) (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "L_w3") (.var "L_w3")) (.num "5.0")))))),
      ("FINE", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5.0"))) (.bin "+" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5.0"))) (.num "0.085"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5.0"))) (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2.0")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4.0"))) (.bin "*" (.bin "*" (.var "L_w3") (.var "L_w3")) (.num "5.0"))))))] }

/-- The finder's witness (kind A). -/
def sat_detumble_phases_m020_wit : RefWitE :=
  { kind := "A", u := 0, m := 1, q0 := 0, k := 0,
    wL := [(-1/4 : ℚ), (1/25 : ℚ), (1/50 : ℚ), (0 : ℚ)],
    wR := [(3/100 : ℚ), (3/100 : ℚ), (4/25 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
