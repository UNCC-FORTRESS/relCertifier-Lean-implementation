/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias_m003`: a mutant of `h2_refuel_ambientbias` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_p (+ R_p 2.9)) [<=->>=]` of `benchmarks/suite_v2/h2_refuel_ambientbias`; file `benchmarks/refute_mutants/h2_refuel_ambientbias_m003/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/h2_refuel_ambientbias_m003/input.txt` (do not edit). -/
def h2_refuel_ambientbias_m003_IRm : PProblem :=
  {
    name := "h2_refuel_ambientbias"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STAGE1"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "20") (.var "p"))))]
          guard := (.cmp "<" (.var "p") (.num "18.0"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE1", "STAGE2"] },
        {
          name := "STAGE2"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "40") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "18.0")) (.cmp "<" (.var "p") (.num "38.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE2", "STAGE3"] },
        {
          name := "STAGE3"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "60") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "38.0")) (.cmp "<" (.var "p") (.num "58.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE3", "TOPOFF"] },
        {
          name := "TOPOFF"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "72.9") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "58.0")) (.cmp "<" (.var "p") (.num "72.4")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["TOPOFF", "COMPLETE"] },
        {
          name := "COMPLETE"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp ">=" (.var "p") (.num "72.4"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["COMPLETE"] } ] }
    R := {
      stateVars := ["p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STAGE1"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "20") (.var "p"))))]
          guard := (.cmp "<" (.var "p") (.num "18.0"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE1", "STAGE2"] },
        {
          name := "STAGE2"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "40") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "18.0")) (.cmp "<" (.var "p") (.num "38.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE2", "STAGE3"] },
        {
          name := "STAGE3"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "60") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "38.0")) (.cmp "<" (.var "p") (.num "58.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE3", "TOPOFF"] },
        {
          name := "TOPOFF"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "70.5") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "58.0")) (.cmp "<" (.var "p") (.num "70.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["TOPOFF", "COMPLETE"] },
        {
          name := "COMPLETE"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp ">=" (.var "p") (.num "70.0"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["COMPLETE"] } ] }
    invariants := [
      ("STAGE1", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "0.00")))),
      ("STAGE2", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "0.00")))),
      ("STAGE3", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "0.00")))),
      ("TOPOFF", (.and (.cmp ">=" (.var "L_p") (.bin "+" (.var "R_p") (.num "2.9"))) (.cmp ">=" (.var "R_p") (.num "58.0")))),
      ("COMPLETE", (.and (.cmp ">=" (.var "L_p") (.bin "+" (.var "R_p") (.num "2.9"))) (.cmp ">=" (.var "R_p") (.num "58.0"))))] }

/-- The finder's witness (kind C). -/
def h2_refuel_ambientbias_m003_wit : RefWitE :=
  { kind := "C", u := 2, m := 3, q0 := 3, k := 0,
    wL := [(58 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(58 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
