/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss_m096`: a mutant of `platoon3_linkloss` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (- (- L_g1 R_g1) (- 0.0 1.0)) 6.0) [<=->>=]` of `benchmarks/suite_v2/platoon3_linkloss`; file `benchmarks/refute_mutants/platoon3_linkloss_m096/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/platoon3_linkloss_m096/input.txt` (do not edit). -/
def platoon3_linkloss_m096_IRm : PProblem :=
  {
    name := "platoon3_linkloss"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["g1", "r1", "g2", "r2", "g3", "r3"]
      epsilon := "2.0"
      modes := [
        {
          name := "FOLLOW"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "29.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "29.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "29.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "19.0")) (.cmp "<=" (.var "g1") (.num "59.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "58.0"))) (.cmp ">=" (.var "g2") (.num "19.0"))) (.cmp "<=" (.var "g2") (.num "59.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "58.0"))) (.cmp ">=" (.var "g3") (.num "19.0"))) (.cmp "<=" (.var "g3") (.num "59.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "58.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["FOLLOW", "LOST"] },
        {
          name := "LOST"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "35.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "29.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "29.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "25.0")) (.cmp "<=" (.var "g1") (.num "59.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "58.0"))) (.cmp ">=" (.var "g2") (.num "19.0"))) (.cmp "<=" (.var "g2") (.num "59.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "58.0"))) (.cmp ">=" (.var "g3") (.num "19.0"))) (.cmp "<=" (.var "g3") (.num "59.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "20.0"))) (.cmp "<=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "58.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["LOST"] } ] }
    R := {
      stateVars := ["g1", "r1", "g2", "r2", "g3", "r3"]
      epsilon := "1.0"
      modes := [
        {
          name := "FOLLOW"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "20.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "59.0"))) (.cmp ">=" (.var "g2") (.num "20.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "59.0"))) (.cmp ">=" (.var "g3") (.num "20.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "59.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["FOLLOW", "BRAKE1", "BRAKE2", "BRAKE3"] },
        {
          name := "BRAKE1"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "*" (.num "-0.5") (.var "r1"))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "g1") (.num "20.0")) (.cmp "<" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "20.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "0.0"))) (.cmp ">=" (.var "g2") (.num "20.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "59.0"))) (.cmp ">=" (.var "g3") (.num "20.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "59.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE1"] },
        {
          name := "BRAKE2"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "*" (.num "-0.5") (.var "r2"))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "g2") (.num "20.0")) (.cmp "<" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "20.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "0.0"))) (.cmp ">=" (.var "g1") (.num "20.0"))) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "59.0"))) (.cmp ">=" (.var "g3") (.num "20.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "59.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE2"] },
        {
          name := "BRAKE3"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "*" (.num "-0.5") (.var "r3")))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "g3") (.num "20.0")) (.cmp "<" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "20.0"))) (.cmp ">=" (.bin "+" (.var "g3") (.bin "*" (.num "2.0") (.var "r3"))) (.num "0.0"))) (.cmp ">=" (.var "g1") (.num "20.0"))) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g1") (.bin "*" (.num "2.0") (.var "r1"))) (.num "59.0"))) (.cmp ">=" (.var "g2") (.num "20.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "21.0"))) (.cmp "<=" (.bin "+" (.var "g2") (.bin "*" (.num "2.0") (.var "r2"))) (.num "59.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE3"] } ] }
    invariants := [
      ("FOLLOW", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0")) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0")))),
      ("LOST", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.num "0.0")) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.bin "-" (.num "0.0") (.num "1.5")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.bin "-" (.num "0.0") (.num "3.0")))) (.cmp ">=" (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))) (.num "6.0"))) (.cmp ">=" (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))))] }

/-- The finder's witness (kind C). -/
def platoon3_linkloss_m096_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 0, k := 0,
    wL := [(497/16 : ℚ), (-259/64 : ℚ), (19 : ℚ), (1/2 : ℚ), (19 : ℚ), (1/2 : ℚ)],
    wR := [(513/16 : ℚ), (-259/64 : ℚ), (20 : ℚ), (1/2 : ℚ), (20 : ℚ), (1/2 : ℚ)] }

end RelCertifier.Refute
