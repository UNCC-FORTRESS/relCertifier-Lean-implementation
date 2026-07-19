/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung2` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_chain_rung2/input.txt` (do not edit). -/
def arm_chain_rung2_IR : PProblem :=
  {
    name := "arm_chain_rung2"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachB", "ApproachA"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachC", "ApproachB"] },
        {
          name := "ApproachC"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Hold", "ApproachC"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "0.95")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Hold"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachFast"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachSlow", "ApproachFast"] },
        {
          name := "ApproachSlow"
          odes := [("theta", (.num "0.3"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "ApproachSlow"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachSlow", "Return"] } ] }
    invariants := [
      ("ApproachA", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("ApproachB", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("ApproachC", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("Hold", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30"))))] }

end RelCertifier.Parse
