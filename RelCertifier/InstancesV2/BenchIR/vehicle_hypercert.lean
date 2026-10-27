/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py vehicle_hypercert`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/vehicle_hypercert/input.txt` (do not edit). -/
def vehicle_hypercert_IRv2 : PProblem :=
  {
    name := "vehicle_hypercert"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["s", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Am4"
          odes := [("s", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.04")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.04")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Am2"
          odes := [("s", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.02")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.02")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "A0"
          odes := [("s", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap2"
          odes := [("s", (.var "v")),
            ("v", (.num "0.02"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.58")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap4"
          odes := [("s", (.var "v")),
            ("v", (.num "0.04"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.56")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] } ] }
    R := {
      stateVars := ["s", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Am4"
          odes := [("s", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.04")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.04")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Am2"
          odes := [("s", (.var "v")),
            ("v", (.bin "-" (.num "0.0") (.num "0.02")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.02")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "A0"
          odes := [("s", (.var "v")),
            ("v", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap2"
          odes := [("s", (.var "v")),
            ("v", (.num "0.02"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.58")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] },
        {
          name := "Ap4"
          odes := [("s", (.var "v")),
            ("v", (.num "0.04"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.56")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.6")))
          next := ["Am4", "Am2", "A0", "Ap2", "Ap4"] } ] }
    invariants := [
      ("Am4", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "+" (.var "L_s") (.num "2.0")) (.var "R_s"))) (.cmp "<=" (.var "R_s") (.bin "+" (.var "L_s") (.num "2.0"))))),
      ("Am2", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "+" (.var "L_s") (.num "2.0")) (.var "R_s"))) (.cmp "<=" (.var "R_s") (.bin "+" (.var "L_s") (.num "2.0"))))),
      ("A0", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "+" (.var "L_s") (.num "2.0")) (.var "R_s"))) (.cmp "<=" (.var "R_s") (.bin "+" (.var "L_s") (.num "2.0"))))),
      ("Ap2", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "+" (.var "L_s") (.num "2.0")) (.var "R_s"))) (.cmp "<=" (.var "R_s") (.bin "+" (.var "L_s") (.num "2.0"))))),
      ("Ap4", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.bin "+" (.var "L_s") (.num "2.0")) (.var "R_s"))) (.cmp "<=" (.var "R_s") (.bin "+" (.var "L_s") (.num "2.0")))))] }

end RelCertifier.Parse
