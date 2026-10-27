/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rampmeter_poll_2to1` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rampmeter_poll_2to1`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rampmeter_poll_2to1/input.txt` (do not edit). -/
def rampmeter_poll_2to1_IRv2 : PProblem :=
  {
    name := "rampmeter_poll_2to1"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["kd", "k1", "k"]
      epsilon := "40"
      modes := [
        {
          name := "R1800"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "15")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "k") (.num "19")) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] },
        {
          name := "R1440"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "12")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "19")) (.cmp "<" (.var "k") (.num "24"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] },
        {
          name := "R1200"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "10")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "24")) (.cmp "<" (.var "k") (.num "29"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] },
        {
          name := "R960"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "8")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "29")) (.cmp "<" (.var "k") (.num "34"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] },
        {
          name := "R720"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "6")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "34")) (.cmp "<" (.var "k") (.num "39"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] },
        {
          name := "R480"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "4")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "39")) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200", "R960", "R720", "R480"] } ] }
    R := {
      stateVars := ["kd", "k1", "k"]
      epsilon := "20"
      modes := [
        {
          name := "R1800"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "15")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "k") (.num "19")) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200"] },
        {
          name := "R1440"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "12")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "19")) (.cmp "<" (.var "k") (.num "24"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1800", "R1440", "R1200"] },
        {
          name := "R1200"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "10")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "24")) (.cmp "<" (.var "k") (.num "29"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1440", "R1200", "R960"] },
        {
          name := "R960"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "8")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "29")) (.cmp "<" (.var "k") (.num "34"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R1200", "R960", "R720"] },
        {
          name := "R720"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "6")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "34")) (.cmp "<" (.var "k") (.num "39"))) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R960", "R720", "R480"] },
        {
          name := "R480"
          odes := [("kd", (.num "0.0")),
            ("k1", (.bin "*" (.num "0.02") (.bin "-" (.var "kd") (.var "k1")))),
            ("k", (.bin "*" (.num "0.01") (.bin "-" (.bin "+" (.var "k1") (.num "4")) (.var "k"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "k") (.num "39")) (.cmp ">=" (.var "kd") (.num "10"))) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "kd") (.num "10")) (.cmp "<=" (.var "kd") (.num "27.5"))) (.cmp ">=" (.var "k1") (.num "10"))) (.cmp "<=" (.var "k1") (.num "27.5"))) (.cmp ">=" (.var "k") (.num "14"))) (.cmp "<=" (.var "k") (.num "42.5")))
          next := ["R960", "R720", "R480"] } ] }
    invariants := [
      ("R1800", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10"))))),
      ("R1440", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10"))))),
      ("R1200", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10"))))),
      ("R960", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10"))))),
      ("R720", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10"))))),
      ("R480", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_kd") (.var "R_kd")) (.cmp "<=" (.var "R_kd") (.var "L_kd"))) (.cmp "<=" (.var "L_k1") (.var "R_k1"))) (.cmp "<=" (.var "R_k1") (.var "L_k1"))) (.cmp "<=" (.var "L_k") (.bin "+" (.var "R_k") (.num "10")))) (.cmp "<=" (.var "R_k") (.bin "+" (.var "L_k") (.num "10")))))] }

end RelCertifier.Parse
