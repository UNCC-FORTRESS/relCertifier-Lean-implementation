/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py sat_detumble_weak`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/sat_detumble_weak/input.txt` (do not edit). -/
def sat_detumble_weak_IRv2 : PProblem :=
  {
    name := "sat_detumble_weak"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["w1", "w2", "w3", "h"]
      epsilon := "2.0"
      modes := [
        {
          name := "DETUMBLE"
          odes := [("w1", (.bin "-" (.bin "-" (.bin "*" (.num "-0.5") (.bin "*" (.var "w2") (.var "w3"))) (.bin "*" (.num "0.5") (.bin "*" (.var "w2") (.var "h")))) (.bin "*" (.num "0.4") (.var "w1")))),
            ("w2", (.bin "-" (.bin "+" (.bin "*" (.num "0.75") (.bin "*" (.var "w3") (.var "w1"))) (.bin "*" (.num "0.25") (.bin "*" (.var "w1") (.var "h")))) (.bin "*" (.num "0.4") (.var "w2")))),
            ("w3", (.bin "-" (.bin "*" (.num "-0.4") (.bin "*" (.var "w1") (.var "w2"))) (.bin "*" (.num "0.4") (.var "w3")))),
            ("h", (.bin "*" (.num "2.0") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["DETUMBLE"] } ] }
    R := {
      stateVars := ["w1", "w2", "w3", "h"]
      epsilon := "1.0"
      modes := [
        {
          name := "NOMINAL"
          odes := [("w1", (.bin "*" (.num "-0.5") (.var "w1"))),
            ("w2", (.bin "*" (.num "-0.5") (.var "w2"))),
            ("w3", (.bin "*" (.num "-0.5") (.var "w3"))),
            ("h", (.bin "*" (.num "2.5") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["NOMINAL", "ECONOMY", "SURVIVAL", "SAFE"] },
        {
          name := "ECONOMY"
          odes := [("w1", (.bin "*" (.num "-0.45") (.var "w1"))),
            ("w2", (.bin "*" (.num "-0.45") (.var "w2"))),
            ("w3", (.bin "*" (.num "-0.45") (.var "w3"))),
            ("h", (.bin "*" (.num "2.25") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["ECONOMY", "NOMINAL", "SAFE"] },
        {
          name := "SURVIVAL"
          odes := [("w1", (.bin "*" (.num "-0.42") (.var "w1"))),
            ("w2", (.bin "*" (.num "-0.42") (.var "w2"))),
            ("w3", (.bin "*" (.num "-0.42") (.var "w3"))),
            ("h", (.bin "*" (.num "2.1") (.var "w3")))]
          guard := (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["SURVIVAL", "NOMINAL", "SAFE"] },
        {
          name := "SAFE"
          odes := [("w1", (.num "0")),
            ("w2", (.num "0")),
            ("w3", (.num "0")),
            ("h", (.num "0"))]
          guard := (.cmp ">" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "w1") (.num "-1.0")) (.cmp "<=" (.var "w1") (.num "1.0"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.0"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.0"))) (.cmp ">=" (.var "h") (.num "-2.0"))) (.cmp "<=" (.var "h") (.num "2.0")))
          next := ["SAFE"] } ] }
    invariants := [
      ("DETUMBLE", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "L_w3") (.var "L_w3")) (.num "5"))) (.bin "+" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5"))) (.num "0.205"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "R_w1") (.var "R_w1")) (.num "2")) (.bin "*" (.bin "*" (.var "R_w2") (.var "R_w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "R_w3") (.var "R_w3")) (.num "5"))) (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "L_w1") (.var "L_w1")) (.num "2")) (.bin "*" (.bin "*" (.var "L_w2") (.var "L_w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "L_w3") (.var "L_w3")) (.num "5"))))))] }

end RelCertifier.Parse
