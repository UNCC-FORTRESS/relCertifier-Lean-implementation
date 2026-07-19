/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/watertank/input.txt` (do not edit). -/
def watertank_IR : PProblem :=
  {
    name := "watertank"
    lambdaMin := "1.0"
    lambdaMax := "10.0"
    L := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.6") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<" (.var "x") (.num "13.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "Low"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "13.0")) (.cmp "<" (.var "x") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.1") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "20.0")) (.cmp "<" (.var "x") (.num "22.45")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.5") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<" (.var "x") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "Low"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.1") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "17.0")) (.cmp "<" (.var "x") (.num "22.45")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] } ] }
    invariants := [
      ("Low", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3")))),
      ("Mid", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3")))),
      ("High", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))))] }

end RelCertifier.Parse
