/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_profiles_m000`: a mutant of `arm_plateau_profiles` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_theta (+ R_theta 0.255)) [<=->>=]` of `benchmarks/suite_v2/arm_plateau_profiles`; file `benchmarks/refute_mutants/arm_plateau_profiles_m000/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/arm_plateau_profiles_m000/input.txt` (do not edit). -/
def arm_plateau_profiles_m000_IRm : PProblem :=
  {
    name := "arm_plateau_profiles"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "2.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-0.5") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.5") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-0.5") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.5") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.855"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachB", "ApproachA", "ApproachCfast", "ApproachCslow", "Hold"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachCfast", "ApproachCslow", "ApproachB", "Hold"] },
        {
          name := "ApproachCfast"
          odes := [("theta", (.num "0.25"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachCfast"] },
        {
          name := "ApproachCslow"
          odes := [("theta", (.num "0.15"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachCslow"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp ">=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.255")))),
      ("Brake", (.cmp ">=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.255"))))] }

/-- The finder's witness (kind B). -/
def arm_plateau_profiles_m000_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 0, k := 0,
    wL := [(1/2 : ℚ), (-1/2 : ℚ)],
    wR := [(49/200 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
