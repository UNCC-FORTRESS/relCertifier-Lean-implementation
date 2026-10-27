/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py engine_start_highidle`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/engine_start_highidle/input.txt` (do not edit). -/
def engine_start_highidle_IRv2 : PProblem :=
  {
    name := "engine_start_highidle"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["n"]
      epsilon := "1.0"
      modes := [
        {
          name := "STARTER"
          odes := [("n", (.bin "*" (.num "0.1") (.bin "-" (.num "30") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "5.0")) (.cmp "<" (.var "n") (.num "25.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["STARTER", "LIGHTOFF", "ABORT"] },
        {
          name := "LIGHTOFF"
          odes := [("n", (.bin "*" (.num "0.08") (.bin "-" (.num "55") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "25.0")) (.cmp "<" (.var "n") (.num "50.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["LIGHTOFF", "SELF", "ABORT"] },
        {
          name := "SELF"
          odes := [("n", (.bin "*" (.num "0.15") (.bin "-" (.num "66") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "50.0")) (.cmp "<" (.var "n") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["SELF", "IDLE"] },
        {
          name := "IDLE"
          odes := [("n", (.bin "*" (.num "0.5") (.bin "-" (.num "66") (.var "n"))))]
          guard := (.cmp ">=" (.var "n") (.num "60.0"))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["IDLE"] },
        {
          name := "ABORT"
          odes := [("n", (.bin "*" (.neg (.num "0.2")) (.var "n")))]
          guard := (.cmp "<" (.var "n") (.num "5.0"))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["ABORT"] } ] }
    R := {
      stateVars := ["n"]
      epsilon := "1.0"
      modes := [
        {
          name := "STARTER"
          odes := [("n", (.bin "*" (.num "0.1") (.bin "-" (.num "30") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "5.0")) (.cmp "<" (.var "n") (.num "25.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["STARTER", "LIGHTOFF", "ABORT"] },
        {
          name := "LIGHTOFF"
          odes := [("n", (.bin "*" (.num "0.08") (.bin "-" (.num "55") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "25.0")) (.cmp "<" (.var "n") (.num "50.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["LIGHTOFF", "SELF", "ABORT"] },
        {
          name := "SELF"
          odes := [("n", (.bin "*" (.num "0.15") (.bin "-" (.num "62") (.var "n"))))]
          guard := (.and (.cmp ">=" (.var "n") (.num "50.0")) (.cmp "<" (.var "n") (.num "60.0")))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["SELF", "IDLE"] },
        {
          name := "IDLE"
          odes := [("n", (.bin "*" (.num "0.5") (.bin "-" (.num "62") (.var "n"))))]
          guard := (.cmp ">=" (.var "n") (.num "60.0"))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["IDLE"] },
        {
          name := "ABORT"
          odes := [("n", (.bin "*" (.neg (.num "0.2")) (.var "n")))]
          guard := (.cmp "<" (.var "n") (.num "5.0"))
          evolve := (.and (.cmp ">=" (.var "n") (.num "0.0")) (.cmp "<=" (.var "n") (.num "110.0")))
          next := ["ABORT"] } ] }
    invariants := [
      ("STARTER", (.cmp "<=" (.var "L_n") (.var "R_n"))),
      ("LIGHTOFF", (.cmp "<=" (.var "L_n") (.var "R_n"))),
      ("SELF", (.cmp "<=" (.var "L_n") (.bin "+" (.var "R_n") (.num "4.0")))),
      ("IDLE", (.cmp "<=" (.var "L_n") (.bin "+" (.var "R_n") (.num "4.0")))),
      ("ABORT", (.cmp "<=" (.var "L_n") (.bin "+" (.var "R_n") (.num "4.0"))))] }

end RelCertifier.Parse
