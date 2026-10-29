/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_tapers_m003`: a mutant of `charger_fast_tapers` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_x (+ R_x 2.0)) [<=->>=]` of `benchmarks/suite_v2/charger_fast_tapers`; file `benchmarks/refute_mutants/charger_fast_tapers_m003/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/charger_fast_tapers_m003/input.txt` (do not edit). -/
def charger_fast_tapers_m003_IRm : PProblem :=
  {
    name := "charger_fast_tapers"
    lambdaMin := "1.25"
    lambdaMax := "1.25"
    L := {
      stateVars := ["x"]
      epsilon := "0.012"
      modes := [
        {
          name := "PRECHARGE"
          odes := [("x", (.bin "*" (.num "0.2") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "15.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["BULK", "PRECHARGE", "FAULT"] },
        {
          name := "BULK"
          odes := [("x", (.bin "*" (.num "0.125") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "15.0")) (.cmp "<" (.var "x") (.num "80.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["ABSORB", "BULK", "FAULT"] },
        {
          name := "ABSORB"
          odes := [("x", (.bin "*" (.num "0.05") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "80.0")) (.cmp "<" (.var "x") (.num "99.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL", "ABSORB"] },
        {
          name := "FULL"
          odes := [("x", (.num "0"))]
          guard := (.cmp ">=" (.var "x") (.num "99.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL"] },
        {
          name := "FAULT"
          odes := [("x", (.bin "*" (.num "-0.01") (.var "x")))]
          guard := (.cmp "<" (.var "x") (.num "10.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FAULT"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "0.006"
      modes := [
        {
          name := "PRECHARGE"
          odes := [("x", (.bin "*" (.num "0.2") (.bin "-" (.num "20.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "15.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["BULK", "PRECHARGE", "FAULT"] },
        {
          name := "BULK"
          odes := [("x", (.bin "*" (.num "0.1") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "15.0")) (.cmp "<" (.var "x") (.num "80.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["ABSORB_SLOW", "ABSORB_FAST", "BULK", "FAULT"] },
        {
          name := "ABSORB_SLOW"
          odes := [("x", (.bin "*" (.num "0.05") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "80.0")) (.cmp "<" (.var "x") (.num "99.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL", "ABSORB_SLOW"] },
        {
          name := "ABSORB_FAST"
          odes := [("x", (.bin "*" (.num "0.07") (.bin "-" (.num "100.0") (.var "x"))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "80.0")) (.cmp "<" (.var "x") (.num "99.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL", "ABSORB_FAST"] },
        {
          name := "FULL"
          odes := [("x", (.num "0"))]
          guard := (.cmp ">=" (.var "x") (.num "99.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FULL"] },
        {
          name := "FAULT"
          odes := [("x", (.bin "*" (.num "-0.01") (.var "x")))]
          guard := (.cmp "<" (.var "x") (.num "10.0"))
          evolve := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<=" (.var "x") (.num "100.0")))
          next := ["FAULT"] } ] }
    invariants := [
      ("PRECHARGE", (.cmp "<=" (.var "L_x") (.var "R_x"))),
      ("BULK", (.cmp ">=" (.var "L_x") (.bin "+" (.var "R_x") (.num "2.0")))),
      ("ABSORB", (.cmp ">=" (.var "L_x") (.bin "+" (.var "R_x") (.num "2.0")))),
      ("FULL", (.cmp ">=" (.var "L_x") (.bin "+" (.var "R_x") (.num "2.0")))),
      ("FAULT", (.cmp ">=" (.var "L_x") (.bin "+" (.var "R_x") (.num "2.0"))))] }

/-- The finder's witness (kind C). -/
def charger_fast_tapers_m003_wit : RefWitE :=
  { kind := "C", u := 0, m := 4, q0 := 0, k := 0,
    wL := [(0 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(10 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
