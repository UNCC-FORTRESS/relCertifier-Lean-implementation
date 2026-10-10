/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon3_linkloss`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/platoon3_linkloss/input.txt` (do not edit). -/
def platoon3_linkloss_IRv2 : PProblem :=
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
            ("r1", (.num "4.0")),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.cmp "<" (.var "g1") (.num "20.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE1"] },
        {
          name := "BRAKE2"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "+" (.bin "+" (.bin "*" (.num "0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1"))) (.num "4.0"))),
            ("g3", (.var "r3")),
            ("r3", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g3") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r3"))))]
          guard := (.cmp "<" (.var "g2") (.num "20.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE2"] },
        {
          name := "BRAKE3"
          odes := [("g1", (.var "r1")),
            ("r1", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1")))),
            ("g2", (.var "r2")),
            ("r2", (.bin "-" (.bin "*" (.num "-0.125") (.bin "-" (.var "g2") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r2")))),
            ("g3", (.var "r3")),
            ("r3", (.bin "+" (.bin "+" (.bin "+" (.bin "+" (.bin "*" (.num "0.125") (.bin "-" (.var "g1") (.num "30.0"))) (.bin "*" (.num "0.75") (.var "r1"))) (.bin "*" (.num "0.125") (.bin "-" (.var "g2") (.num "30.0")))) (.bin "*" (.num "0.75") (.var "r2"))) (.num "4.0")))]
          guard := (.cmp "<" (.var "g3") (.num "20.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "g1") (.num "0.0")) (.cmp "<=" (.var "g1") (.num "60.0"))) (.cmp ">=" (.var "r1") (.num "-10.0"))) (.cmp "<=" (.var "r1") (.num "10.0"))) (.cmp ">=" (.var "g2") (.num "0.0"))) (.cmp "<=" (.var "g2") (.num "60.0"))) (.cmp ">=" (.var "r2") (.num "-10.0"))) (.cmp "<=" (.var "r2") (.num "10.0"))) (.cmp ">=" (.var "g3") (.num "0.0"))) (.cmp "<=" (.var "g3") (.num "60.0"))) (.cmp ">=" (.var "r3") (.num "-10.0"))) (.cmp "<=" (.var "r3") (.num "10.0")))
          next := ["BRAKE3"] } ] }
    invariants := [
      ("FOLLOW", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0")) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0")))),
      ("LOST", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.num "0.0")) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.bin "-" (.num "0.0") (.num "1.5")))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r1") (.var "R_r1")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.num "5.0")))) (.bin "-" (.num "0.0") (.num "3.0")))) (.cmp "<=" (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))) (.num "6.0"))) (.cmp ">=" (.bin "-" (.bin "-" (.var "L_g1") (.var "R_g1")) (.bin "-" (.num "0.0") (.num "1.0"))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r2") (.var "R_r2")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g2") (.var "R_g2")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp "<=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))) (.cmp ">=" (.bin "+" (.bin "-" (.var "L_r3") (.var "R_r3")) (.bin "*" (.num "0.5") (.bin "-" (.bin "-" (.var "L_g3") (.var "R_g3")) (.bin "-" (.num "0.0") (.num "1.0"))))) (.num "0.0"))))] }

end RelCertifier.Parse
