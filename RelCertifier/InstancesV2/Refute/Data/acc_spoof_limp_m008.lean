/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp_m008`: a mutant of `acc_spoof_limp` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= R_v (+ L_v 12.0)) [<=->>=]` of `benchmarks/suite_v2/acc_spoof_limp`; file `benchmarks/refute_mutants/acc_spoof_limp_m008/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/acc_spoof_limp_m008/input.txt` (do not edit). -/
def acc_spoof_limp_m008_IRm : PProblem :=
  {
    name := "acc_spoof_limp"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.bin "*" (.num "1.25") (.var "v")))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<" (.var "v") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["CRUISE", "LIMP"] },
        {
          name := "LIMP"
          odes := [("v", (.bin "*" (.num "0.3") (.bin "-" (.num "22.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<=" (.var "v") (.num "30.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["LIMP"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "1.0"
      modes := [
        {
          name := "NORMAL"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "30.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<" (.var "v") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["NORMAL", "ECO", "SPORT", "DISENGAGE"] },
        {
          name := "ECO"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "27.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<" (.var "v") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["ECO", "NORMAL", "DISENGAGE"] },
        {
          name := "SPORT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "33.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "20.0")) (.cmp "<" (.var "v") (.num "40.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["SPORT", "NORMAL", "DISENGAGE"] },
        {
          name := "DISENGAGE"
          odes := [("v", (.bin "*" (.num "-0.5") (.var "v")))]
          guard := (.cmp "<" (.var "v") (.num "20.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["DISENGAGE"] } ] }
    invariants := [
      ("CRUISE", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.bin "+" (.var "L_v") (.num "9.0"))))),
      ("LIMP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp ">=" (.var "R_v") (.bin "+" (.var "L_v") (.num "12.0")))))] }

/-- The finder's witness (kind C). -/
def acc_spoof_limp_m008_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 0, k := 0,
    wL := [(30 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(30 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
